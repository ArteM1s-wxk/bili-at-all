// ==UserScript==
// @name         B站评论区一键@好友
// @namespace    https://github.com/ArteM1s-wxk/bili-at-all
// @version      0.10.0
// @description  B站视频评论区一键@群友：在设置界面维护 UID 列表，脚本自动解析为当前昵称，右下角一键把 @昵称 插入评论框（纯文本粘贴，由 B 站编辑器转真实提及节点），超长自动分批，由用户手动发送。
// @author       ArteM1s-wxk
// @homepageURL  https://github.com/ArteM1s-wxk/bili-at-all
// @supportURL   https://github.com/ArteM1s-wxk/bili-at-all/issues
// @match        *://www.bilibili.com/video/*
// @match        *://bilibili.com/video/*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @grant        GM_xmlhttpRequest
// @connect      api.bilibili.com
// @connect      bilibili.com
// @run-at       document-idle
// @license      MIT
// ==/UserScript==

(function () {
  'use strict';

  // =====================================================================
  // 常量
  // =====================================================================
  var COMMENT_LIMIT = 1000;          // B站单条评论字数上限（分批阈值）
  var CACHE_TTL_MS = 24 * 60 * 60 * 1000; // 昵称缓存有效期（24 小时）
  var CONCURRENCY = 10;              // 解析昵称的最大并发请求数
  var STORAGE_UIDS = 'biliAtAll_uids';
  var STORAGE_CACHE = 'biliAtAll_cache';
  var API_CARD = 'https://api.bilibili.com/x/web-interface/card';

  // =====================================================================
  // 纯逻辑（可单测）
  // =====================================================================

  /** 解析设置文本为 UID 数组：按行/空白/中英文逗号分号分隔，去重保序，过滤非纯数字 */
  function parseUidList(text) {
    var tokens = String(text || '').split(/[\s,，;；]+/);
    var seen = {};
    var out = [];
    for (var i = 0; i < tokens.length; i++) {
      var t = tokens[i].trim();
      if (/^\d+$/.test(t) && !seen[t]) {
        seen[t] = true;
        out.push(t);
      }
    }
    return out;
  }

  /** 把昵称数组拼成 "@昵称 " 串（每个昵称后带一个空格，作为@解析的结束符） */
  function formatMentions(names) {
    var s = '';
    for (var i = 0; i < names.length; i++) {
      s += '@' + names[i] + ' ';
    }
    return s;
  }

  /**
   * 把昵称列表按 maxLen 分组，保证每组拼接后的长度 <= maxLen。
   * 单个昵称本身超过 maxLen 时也独立成组（不丢人，交给用户处理）。
   * 返回数组的数组（每组是昵称子集）。
   */
  function buildBatchNameGroups(names, maxLen) {
    var groups = [];
    var cur = [];
    var curLen = 0;
    for (var i = 0; i < names.length; i++) {
      var piece = '@' + names[i] + ' ';
      var addLen = curLen + piece.length;
      if (cur.length > 0 && addLen > maxLen) {
        groups.push(cur.slice());
        cur = [];
        curLen = 0;
      }
      cur.push(names[i]);
      curLen += piece.length;
    }
    if (cur.length > 0) groups.push(cur);
    return groups;
  }

  /** 把昵称列表按 maxLen 分批为可直接插入的字符串 */
  function buildBatches(names, maxLen) {
    return buildBatchNameGroups(names, maxLen).map(formatMentions);
  }

  /** 简易并发限流池：最多 limit 个任务同时进行 */
  function pool(items, limit, fn) {
    var i = 0;
    var n = Math.max(1, Math.min(limit, items.length));
    var workers = [];
    function run() {
      return Promise.resolve().then(function next() {
        if (i >= items.length) return;
        var idx = i++;
        return fn(items[idx], idx).then(next);
      });
    }
    for (var w = 0; w < n; w++) workers.push(run());
    return Promise.all(workers);
  }

  /**
   * 解析 UID → 昵称，带缓存与并发。
   * deps: { getCache(), setCache(cache), fetchName(uid):Promise<string>, now():number, freshMs:number, concurrency:number }
   * 返回 Promise<{ names:string[], byUid:object, failed:Array<{uid,error}> }>
   * names 保持输入 UID 顺序；失败的 UID 不在 names 中（除非有过期缓存兜底）。
   */
  function resolveNames(uids, deps) {
    var cache = deps.getCache() || {};
    var now = deps.now();
    var freshMs = deps.freshMs;
    var result = { names: [], byUid: {}, failed: [] };
    var toFetch = [];

    for (var i = 0; i < uids.length; i++) {
      var uid = uids[i];
      var c = cache[uid];
      if (c && c.name && (now - c.ts) < freshMs) {
        result.byUid[uid] = c.name;   // 命中新鲜缓存，不发请求
      } else {
        toFetch.push(uid);
      }
    }

    return pool(toFetch, deps.concurrency, function (uid) {
      return deps.fetchName(uid).then(function (name) {
        if (name) {
          cache[uid] = { name: name, ts: now };
          result.byUid[uid] = name;
        } else {
          throw new Error('返回昵称为空');
        }
      }).catch(function (err) {
        result.failed.push({ uid: uid, error: String((err && err.message) || err) });
        // 过期缓存兜底：重查失败但历史上有过昵称，仍用之
        if (!result.byUid[uid] && cache[uid] && cache[uid].name) {
          result.byUid[uid] = cache[uid].name;
        }
      });
    }).then(function () {
      result.names = uids.map(function (u) { return result.byUid[u]; }).filter(Boolean);
      deps.setCache(cache);
      return result;
    });
  }

  /**
   * 统计编辑器里真实"提及节点"数量：能精确匹配到我们插入名单中某个昵称的叶子元素。
   * 用于验证粘贴是否被 B 站编辑器转换成了可点击的@（而非纯文本）。
   */
  function countConverted(editor, names) {
    var expected = {};
    for (var i = 0; i < names.length; i++) expected[names[i]] = true;
    var count = 0;
    var els = [];
    try { els = Array.prototype.slice.call(editor.querySelectorAll('*')); } catch (e) {}
    for (var j = 0; j < els.length; j++) {
      var el = els[j];
      // 只看没有元素子节点的"叶子"，避免外层容器整个文本以@开头时误计
      if (el.children && el.children.length > 0) continue;
      var txt = (el.textContent || '').trim();
      if (txt.length <= 1) continue;
      var name = txt.charAt(0) === '@' ? txt.slice(1) : txt;
      if (expected[name]) count++;
    }
    return count;
  }

  // =====================================================================
  // 环境封装（GM / storage / fetch）
  // =====================================================================

  function getStoredUids() {
    try {
      var v = GM_getValue(STORAGE_UIDS, []);
      return Array.isArray(v) ? v : [];
    } catch (e) { return []; }
  }

  function setStoredUids(uids) {
    try { GM_setValue(STORAGE_UIDS, uids); } catch (e) {}
  }

  function getCache() {
    try {
      var v = GM_getValue(STORAGE_CACHE, {});
      return v && typeof v === 'object' ? v : {};
    } catch (e) { return {}; }
  }

  function setCache(cache) {
    try { GM_setValue(STORAGE_CACHE, cache); } catch (e) {}
  }

  /** 调 card 接口把单个 UID 解析为当前昵称（无需登录、无 wbi）。失败抛错。 */
  function fetchNameByCard(uid) {
    return new Promise(function (resolve, reject) {
      try {
        GM_xmlhttpRequest({
          method: 'GET',
          url: API_CARD + '?mid=' + encodeURIComponent(uid) + '&photo=false',
          responseType: 'json',
          timeout: 15000,
          onload: function (res) {
            var data = res && res.response;
            if (!data || typeof data === 'string') {
              try { data = JSON.parse(res.responseText); } catch (e) { data = null; }
            }
            if (data && data.code === 0 && data.data && data.data.card && data.data.card.name) {
              resolve(String(data.data.card.name));
            } else {
              reject(new Error('code=' + (data && data.code) + (data && data.message ? ' ' + data.message : '')));
            }
          },
          onerror: function () { reject(new Error('请求失败')); },
          ontimeout: function () { reject(new Error('超时')); },
        });
      } catch (e) { reject(e); }
    });
  }

  // =====================================================================
  // DOM 工具（递归穿透 shadow DOM）
  // =====================================================================

  /** 深度优先遍历所有元素（含 shadowRoot 内部），返回匹配的元素数组 */
  function queryAllShadow(root, predicate) {
    var results = [];
    function walk(node) {
      var els = [];
      try { els = Array.prototype.slice.call(node.querySelectorAll ? node.querySelectorAll('*') : []); } catch (e) {}
      for (var i = 0; i < els.length; i++) {
        var el = els[i];
        if (predicate(el)) results.push(el);
        if (el.shadowRoot) walk(el.shadowRoot);
      }
    }
    walk(root);
    return results;
  }

  /** 找到评论输入框（优先有实际布局尺寸的，通常即当前可见评论框），递归穿透 shadow DOM */
  function findEditor(root) {
    var candidates = queryAllShadow(root, function (el) {
      var ce = el.getAttribute && el.getAttribute('contenteditable');
      return (ce !== null && ce !== 'false') && isUsable(el);
    });
    if (candidates.length === 0) return null;
    // 优先选有实际布局的（SPA 里常见隐藏的备用编辑器）；都没有就取最后渲染的
    for (var i = candidates.length - 1; i >= 0; i--) {
      try { if (candidates[i].getClientRects().length > 0) return candidates[i]; } catch (e) {}
    }
    return candidates[candidates.length - 1];
  }

  function isUsable(el) {
    try {
      // isConnected 对 shadow DOM 树内的元素同样返回 true（ownerDocument.contains 会误判为 false）
      if (!el.isConnected) return false;
      var win = el.ownerDocument.defaultView;
      var style = win ? win.getComputedStyle(el) : null;
      if (style) {
        if (style.display === 'none' || style.visibility === 'hidden') return false;
        if (style.opacity !== '' && Number(style.opacity) === 0) return false;
      }
    } catch (e) {}
    return true;
  }

  /** 触发 input 事件（优先 InputEvent，兼容无 InputEvent 的环境） */
  function dispatchInput(el, data, inputType) {
    try {
      el.dispatchEvent(new InputEvent('input', { bubbles: true, data: data, inputType: inputType }));
    } catch (e) {
      el.dispatchEvent(new Event('input', { bubbles: true }));
    }
  }

  /** 让编辑器获得焦点，并把光标放到末尾（追加式插入） */
  function focusAndCaretAtEnd(editor) {
    try {
      var range = document.createRange();
      range.selectNodeContents(editor);
      range.collapse(false);
      var sel = window.getSelection();
      sel.removeAllRanges();
      sel.addRange(range);
    } catch (e) {}
    try { editor.focus({ preventScroll: true }); } catch (e) { try { editor.focus(); } catch (e2) {} }
  }

  function editorText(editor) {
    return editor.textContent || '';
  }

  function tick(ms) {
    return new Promise(function (r) { setTimeout(r, ms); });
  }

  /** 轮询等待编辑器里出现 probe 文本，避免异步处理导致误判失败（进而重复插入） */
  async function waitForText(editor, probe, timeoutMs, intervalMs) {
    var deadline = Date.now() + timeoutMs;
    while (Date.now() < deadline) {
      if (editorText(editor).indexOf(probe) !== -1) return true;
      await tick(intervalMs || 150);
    }
    return editorText(editor).indexOf(probe) !== -1;
  }

  // =====================================================================
  // 插入逻辑（三级兜底）
  // =====================================================================

  /**
   * 把 mentionText 插入编辑器。
   * 1. 优先模拟纯文本粘贴（ClipboardEvent + DataTransfer），B站编辑器会转真实提及节点；
   * 2. 兜底 execCommand('insertText')；
   * 3. 再兜底直接 DOM 插入文本节点 + input 事件。
   * 返回 { ok, method }。
   */
  async function insertIntoEditor(editor, mentionText) {
    focusAndCaretAtEnd(editor);
    var probe = mentionText.slice(0, 20);

    // 方法1：模拟粘贴（B站编辑器会转真实提及节点）。轮询最多 2s，异步转换也等得到。
    try {
      var dt = new DataTransfer();
      dt.setData('text/plain', mentionText);
      var pasteEvt = new ClipboardEvent('paste', { clipboardData: dt, bubbles: true, cancelable: true });
      editor.dispatchEvent(pasteEvt);
      if (await waitForText(editor, probe, 2000)) {
        return { ok: true, method: 'paste' };
      }
    } catch (e) { /* 继续兜底 */ }

    // 方法2：execCommand insertText
    try {
      focusAndCaretAtEnd(editor);
      document.execCommand('insertText', false, mentionText);
      if (await waitForText(editor, probe, 1500)) {
        return { ok: true, method: 'insertText' };
      }
    } catch (e) { /* 继续兜底 */ }

    // 方法3：直接 DOM 插入（光标处插入文本节点）
    try {
      focusAndCaretAtEnd(editor);
      var range = document.createRange();
      range.selectNodeContents(editor);
      range.collapse(false);
      range.insertNode(document.createTextNode(mentionText));
      dispatchInput(editor, mentionText, 'insertText');
      if (await waitForText(editor, probe, 1500)) {
        return { ok: true, method: 'dom' };
      }
    } catch (e) { /* 继续兜底 */ }

    // 方法4：末尾追加文本节点 + input 事件（最保守的兜底）
    try {
      editor.appendChild(document.createTextNode(mentionText));
      dispatchInput(editor, mentionText, 'insertText');
      if (await waitForText(editor, probe, 1500)) {
        return { ok: true, method: 'append' };
      }
    } catch (e) { /* 全部失败 */ }

    return { ok: false, method: 'none' };
  }

  // =====================================================================
  // UI：toast
  // =====================================================================

  var toastEl = null;
  function toast(msg, isError) {
    if (!toastEl) {
      toastEl = document.createElement('div');
      toastEl.style.cssText = [
        'position:fixed', 'left:50%', 'bottom:120px', 'transform:translateX(-50%)',
        'background:' + (isError ? '#c0392b' : '#2c3e50'),
        'color:#fff', 'padding:10px 18px', 'border-radius:8px', 'font-size:14px',
        'z-index:99999', 'box-shadow:0 4px 16px rgba(0,0,0,.3)',
        'max-width:80vw', 'word-break:break-all', 'transition:opacity .3s',
      ].join(';');
      document.body.appendChild(toastEl);
    }
    toastEl.textContent = msg;
    toastEl.style.opacity = '1';
    clearTimeout(toastEl._t);
    toastEl._t = setTimeout(function () { toastEl.style.opacity = '0'; }, 4000);
  }

  // =====================================================================
  // UI：设置界面（模态）
  // =====================================================================

  var settingsEl = null;
  var lastNewlineCount = 0; // 记录打开/上次自动保存时的换行数，用于检测"新增了一行"

  function openSettings() {
    if (!settingsEl) settingsEl = buildSettings();
    settingsEl.style.display = 'flex';
    var ta = settingsEl.querySelector('.baa-ta');
    ta.value = getStoredUids().join('\n');
    lastNewlineCount = countNewlines(ta.value);
    renderResults(settingsEl, parseUidList(ta.value), null);
    ta.focus();
  }

  function closeSettings() {
    if (settingsEl) settingsEl.style.display = 'none';
  }

  function countNewlines(s) {
    return (String(s).match(/\n/g) || []).length;
  }

  /**
   * 把 UID→昵称 结果渲染到设置面板右栏。
   * res 为 null 时按缓存显示（有缓存→绿名，无→灰"待解析"）；
   * res 非 null 时显示本次解析结果：成功→绿名，失败→红字（有旧缓存兜底则橙名提示）。
   */
  function renderResults(overlay, uids, res) {
    var list = overlay.querySelector('.baa-results');
    var statusLine = overlay.querySelector('.baa-status');
    if (!list || !statusLine) return;
    list.innerHTML = '';

    if (uids.length === 0) {
      statusLine.textContent = '暂无 UID，请在左侧输入';
      statusLine.style.color = '#888';
      return;
    }

    var failedMap = {};
    var failedCount = 0;
    if (res && res.failed) {
      failedCount = res.failed.length;
      for (var i = 0; i < res.failed.length; i++) failedMap[res.failed[i].uid] = res.failed[i].error;
    }
    var cache = getCache();

    for (var j = 0; j < uids.length; j++) {
      var uid = uids[j];
      var row = document.createElement('div');
      row.style.cssText = 'display:flex;gap:8px;align-items:center;padding:6px 8px;border-bottom:1px solid #f0f0f0;font-size:13px;';

      var uidSpan = document.createElement('span');
      uidSpan.textContent = uid;
      uidSpan.style.cssText = 'min-width:70px;color:#666;font-family:monospace;';

      var arrow = document.createElement('span');
      arrow.textContent = '→';
      arrow.style.color = '#bbb';

      var nameSpan = document.createElement('span');
      nameSpan.style.wordBreak = 'break-all';
      if (failedMap[uid] !== undefined) {
        var stale = res && res.byUid[uid]; // 解析失败但有过期缓存兜底
        if (stale) {
          nameSpan.textContent = stale + '（缓存，更新失败：' + failedMap[uid] + '）';
          nameSpan.style.color = '#e67e22'; // 橙：用旧缓存但本次更新失败
          nameSpan.title = failedMap[uid];
        } else {
          nameSpan.textContent = '解析失败：' + failedMap[uid];
          nameSpan.style.color = '#c0392b'; // 红
        }
      } else {
        var name = (res && res.byUid[uid]) || (cache[uid] && cache[uid].name);
        if (name) {
          nameSpan.textContent = name + (res && res.byUid[uid] ? '' : '（缓存）');
          nameSpan.style.color = '#27ae60';
          nameSpan.style.fontWeight = '600';
        } else {
          nameSpan.textContent = res ? '解析失败' : '待解析';
          nameSpan.style.color = '#bbb';
        }
      }
      row.appendChild(uidSpan);
      row.appendChild(arrow);
      row.appendChild(nameSpan);
      list.appendChild(row);
    }

    if (res) {
      var okCount = uids.length - failedCount;
      statusLine.textContent = '成功 ' + okCount + ' / 共 ' + uids.length + (failedCount ? '，失败 ' + failedCount : '');
      statusLine.style.color = failedCount ? '#c0392b' : '#27ae60';
    } else {
      statusLine.textContent = '点击「测试解析昵称」获取最新昵称';
      statusLine.style.color = '#888';
    }
  }

  function buildSettings() {
    var overlay = document.createElement('div');
    overlay.style.cssText = [
      'position:fixed', 'inset:0', 'background:rgba(0,0,0,.45)',
      'display:none', 'align-items:center', 'justify-content:center', 'z-index:100000',
    ].join(';');

    var box = document.createElement('div');
    box.style.cssText = [
      'background:#fff', 'color:#222', 'border-radius:12px', 'padding:20px 24px',
      'width:760px', 'max-width:94vw', 'max-height:88vh', 'overflow:auto',
      'font-family:-apple-system,"PingFang SC","Microsoft YaHei",sans-serif',
      'box-shadow:0 8px 40px rgba(0,0,0,.35)',
    ].join(';');

    var title = document.createElement('div');
    title.textContent = 'B站一键@ 设置';
    title.style.cssText = 'font-size:18px;font-weight:700;margin-bottom:4px;';

    var tip = document.createElement('div');
    tip.textContent = '每行一个 UID，换行自动保存，也可点「保存」手动保存。右侧显示 UID → 当前昵称（昵称改动后 24h 内自动刷新）。';
    tip.style.cssText = 'font-size:12px;color:#888;margin-bottom:12px;';

    // 左右两栏：左=输入 UID，右=UID→昵称 结果
    var layout = document.createElement('div');
    layout.style.cssText = 'display:flex;gap:16px;align-items:stretch;margin-bottom:12px;';

    var leftCol = document.createElement('div');
    leftCol.style.cssText = 'flex:1;min-width:0;display:flex;flex-direction:column;';

    var ta = document.createElement('textarea');
    ta.className = 'baa-ta';
    ta.placeholder = '每行一个 UID，例如：\n123456789\n987654321';
    ta.style.cssText = [
      'width:100%', 'height:200px', 'box-sizing:border-box', 'border:1px solid #ddd',
      'border-radius:8px', 'padding:8px', 'font-size:13px', 'resize:vertical',
      'font-family:monospace',
    ].join(';');

    var autosaveHint = document.createElement('div');
    autosaveHint.textContent = '';
    autosaveHint.style.cssText = 'font-size:12px;color:#27ae60;margin-top:4px;min-height:16px;';

    // 换行自动保存：新增一行（换行数增加）即解析并写入存储，不依赖手动保存
    ta.addEventListener('input', function () {
      var nl = countNewlines(ta.value);
      if (nl > lastNewlineCount) {
        lastNewlineCount = nl;
        setStoredUids(parseUidList(ta.value));
        autosaveHint.textContent = '已自动保存 ' + parseUidList(ta.value).length + ' 个 UID';
        clearTimeout(autosaveHint._t);
        autosaveHint._t = setTimeout(function () { autosaveHint.textContent = ''; }, 3000);
      }
    });

    leftCol.appendChild(ta);
    leftCol.appendChild(autosaveHint);

    var rightCol = document.createElement('div');
    rightCol.style.cssText = 'flex:1;min-width:0;display:flex;flex-direction:column;';

    var resHeader = document.createElement('div');
    resHeader.textContent = 'UID → 昵称';
    resHeader.style.cssText = 'font-size:13px;font-weight:700;color:#333;margin-bottom:6px;';

    var status = document.createElement('div');
    status.className = 'baa-status';
    status.style.cssText = 'font-size:12px;margin:0 0 6px 0;min-height:16px;word-break:break-all;';

    var results = document.createElement('div');
    results.className = 'baa-results';
    results.style.cssText = 'flex:1;border:1px solid #eee;border-radius:8px;overflow:auto;max-height:220px;background:#fafafa;';

    rightCol.appendChild(resHeader);
    rightCol.appendChild(status);
    rightCol.appendChild(results);

    layout.appendChild(leftCol);
    layout.appendChild(rightCol);

    var btnRow = document.createElement('div');
    btnRow.style.cssText = 'display:flex;gap:8px;flex-wrap:wrap;';

    function mkBtn(label, style, onClick) {
      var b = document.createElement('button');
      b.textContent = label;
      b.style.cssText = [
        'border:none', 'border-radius:6px', 'padding:8px 14px', 'font-size:13px', 'cursor:pointer', style,
      ].join(';');
      b.addEventListener('click', onClick);
      return b;
    }

    var saveBtn = mkBtn('保存', 'background:#00a1d6;color:#fff;font-weight:600;', function () {
      var uids = parseUidList(ta.value);
      setStoredUids(uids);
      closeSettings();
      toast('已保存 ' + uids.length + ' 个 UID');
    });

    var resolveBtn = mkBtn('测试解析昵称', 'background:#fff;color:#00a1d6;border:1px solid #00a1d6;', async function () {
      var uids = parseUidList(ta.value);
      if (uids.length === 0) { toast('没有可解析的 UID', true); return; }
      resolveBtn.disabled = true;
      resolveBtn.textContent = '解析中…';
      try {
        var res = await resolveNames(uids, {
          getCache: getCache,
          setCache: setCache,
          fetchName: fetchNameByCard,
          now: Date.now,
          freshMs: CACHE_TTL_MS,
          concurrency: CONCURRENCY,
        });
        renderResults(overlay, uids, res);
      } catch (e) {
        toast('解析失败：' + e.message, true);
      } finally {
        resolveBtn.disabled = false;
        resolveBtn.textContent = '测试解析昵称';
      }
    });

    var clearBtn = mkBtn('清空昵称缓存', 'background:#fff;color:#c0392b;border:1px solid #c0392b;', function () {
      setCache({});
      toast('昵称缓存已清空');
      renderResults(overlay, parseUidList(ta.value), null);
    });

    var closeBtn = mkBtn('关闭', 'background:#eee;color:#333;', closeSettings);

    btnRow.appendChild(saveBtn);
    btnRow.appendChild(resolveBtn);
    btnRow.appendChild(clearBtn);
    btnRow.appendChild(closeBtn);

    box.appendChild(title);
    box.appendChild(tip);
    box.appendChild(layout);
    box.appendChild(btnRow);
    overlay.appendChild(box);

    // 点击遮罩关闭
    overlay.addEventListener('click', function (e) { if (e.target === overlay) closeSettings(); });

    document.body.appendChild(overlay);
    return overlay;
  }

  // =====================================================================
  // UI：右下角浮动按钮 + 齿轮
  // =====================================================================

  var btnWrap = null;
  var batchState = null; // { batches:[], idx:number, names:[] }

  function buildFloatingButton() {
    if (btnWrap) return btnWrap;
    btnWrap = document.createElement('div');
    btnWrap.style.cssText = 'position:fixed;right:24px;bottom:80px;z-index:99999;display:flex;flex-direction:column;align-items:center;gap:10px;';

    var atBtn = document.createElement('button');
    atBtn.textContent = '@全部';
    atBtn.title = '一键把好友@插入评论框（发送前请先填写评论内容）';
    atBtn.style.cssText = [
      'width:60px;height:60px;border-radius:50%;border:none;cursor:pointer;',
      'background:linear-gradient(135deg,#00a1d6,#0081b3);color:#fff;',
      'font-size:15px;font-weight:700;box-shadow:0 4px 16px rgba(0,161,214,.5);',
      'transition:transform .15s;',
    ].join(';');
    atBtn.addEventListener('mouseenter', function () { atBtn.style.transform = 'scale(1.06)'; });
    atBtn.addEventListener('mouseleave', function () { atBtn.style.transform = 'scale(1)'; });
    atBtn.addEventListener('click', handleAtClick);

    var gear = document.createElement('button');
    gear.textContent = '⚙';
    gear.title = '设置（UID 列表）';
    gear.style.cssText = [
      'width:32px;height:32px;border-radius:50%;border:none;cursor:pointer;',
      'background:rgba(0,0,0,.55);color:#fff;font-size:15px;',
    ].join(';');
    gear.addEventListener('click', openSettings);

    btnWrap.appendChild(atBtn);
    btnWrap.appendChild(gear);
    document.body.appendChild(btnWrap);
    return btnWrap;
  }

  function updateAtButtonLabel() {
    var btn = btnWrap && btnWrap.querySelector('button');
    if (!btn) return;
    if (batchState && batchState.idx < batchState.batches.length) {
      btn.textContent = '下一批\n' + (batchState.idx + 1) + '/' + batchState.batches.length;
    } else {
      btn.textContent = '@全部';
    }
  }

  // =====================================================================
  // 主流程：点击 @全部
  // =====================================================================

  async function handleAtClick() {
    var uids = getStoredUids();
    if (uids.length === 0) {
      toast('还没有配置 UID，请先点 ⚙ 设置', true);
      openSettings();
      return;
    }

    var editor = findEditor(document);
    if (!editor) {
      toast('没找到评论输入框。请先点击评论区，或确认已登录。', true);
      return;
    }

    // 有未完成的分批 → 插入下一批
    if (batchState && batchState.idx < batchState.batches.length) {
      await insertBatch(editor, batchState.idx);
      return;
    }

    // 重新解析（命中缓存则不发请求）
    toast('正在解析昵称…');
    var res;
    try {
      res = await resolveNames(uids, {
        getCache: getCache,
        setCache: setCache,
        fetchName: fetchNameByCard,
        now: Date.now,
        freshMs: CACHE_TTL_MS,
        concurrency: CONCURRENCY,
      });
    } catch (e) {
      toast('解析失败：' + e.message, true);
      return;
    }

    if (res.names.length === 0) {
      toast('昵称全部解析失败，请到设置里检查 UID 或网络', true);
      return;
    }
    if (res.failed.length > 0) {
      toast('部分解析失败：' + res.failed.map(function (f) { return f.uid; }).join(',') + '，已跳过');
    }

    var batches = buildBatches(res.names, COMMENT_LIMIT);
    batchState = { batches: batches, idx: 0, names: res.names };
    updateAtButtonLabel();
    await insertBatch(editor, 0);
  }

  async function insertBatch(editor, idx) {
    var text = batchState.batches[idx];
    var batchNames = buildBatchNameGroups(batchState.names, COMMENT_LIMIT)[idx] || [];
    var inserted = await insertIntoEditor(editor, text);
    if (!inserted.ok) {
      toast('插入失败：评论框无法写入内容，请手动粘贴', true);
      return;
    }

    var converted = 0;
    if (inserted.method === 'paste') {
      // 只有走粘贴路径才可能有"真实提及节点"，且用户已实测纯文本粘贴会转换。
      // 转换验证是尽力而为：数出精确匹配本批昵称的叶子元素。
      converted = countConverted(editor, batchNames);
    }

    var total = batchState.batches.length;
    if (idx + 1 < total) {
      batchState.idx = idx + 1;
      updateAtButtonLabel();
      toast('第 ' + (idx + 1) + '/' + total + ' 批已插入（' + batchNames.length + ' 人）。发送后点按钮插入下一批。' +
        (inserted.method === 'paste' && converted < batchNames.length
          ? '（转换 ' + converted + '/' + batchNames.length + '，未转换的请检查昵称）' : ''));
    } else {
      var done = batchState.names.length;
      batchState = null;
      updateAtButtonLabel();
      toast('已插入全部 ' + done + ' 人，请确认内容后发送' +
        (inserted.method === 'paste' && converted < batchNames.length
          ? '（转换 ' + converted + '/' + batchNames.length + '，未转换的请检查昵称）' : ''));
    }
  }

  // =====================================================================
  // 初始化
  // =====================================================================

  function init() {
    try { buildFloatingButton(); } catch (e) { console.error('[B站一键@] 浮动按钮初始化失败', e); }
    try {
      GM_registerMenuCommand('⚙ 设置 UID 列表', openSettings);
      GM_registerMenuCommand('@全部 插入评论框', function () { var b = btnWrap && btnWrap.querySelector('button'); if (b) b.click(); });
    } catch (e) {}
  }

  if (typeof document !== 'undefined' && document.body) {
    init();
  } else if (typeof document !== 'undefined') {
    document.addEventListener('DOMContentLoaded', init);
  }

  // =====================================================================
  // 导出纯函数供 node 单测（浏览器环境忽略）
  // =====================================================================
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
      parseUidList: parseUidList,
      formatMentions: formatMentions,
      buildBatchNameGroups: buildBatchNameGroups,
      buildBatches: buildBatches,
      pool: pool,
      resolveNames: resolveNames,
      countConverted: countConverted,
      findEditor: findEditor,
      insertIntoEditor: insertIntoEditor,
      openSettings: openSettings,
      renderResults: renderResults,
      countNewlines: countNewlines,
      COMMENT_LIMIT: COMMENT_LIMIT,
    };
  }
})();
