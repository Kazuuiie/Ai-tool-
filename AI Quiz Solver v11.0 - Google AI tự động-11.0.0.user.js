// ==UserScript==
// @name         AI Quiz Solver v11.0 - Google AI tự động
// @namespace    Kazuuiie
// @version      11.0.0
// @description  Nhận diện nhiều kiểu quiz (radio/checkbox, div, ARIA, A. B. C. D., điền ngắn, đọc được công thức). Có đáp án trong HTML thì tự tick, không có thì tự gửi đề sang Google AI và đọc kết quả về panel. Giao diện mới: Shadow DOM, sáng/tối, tab, vòng tiến độ.
// @match        *://*/*
// @grant        GM_openInTab
// @grant        GM_setClipboard
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_addValueChangeListener
// @run-at       document-idle
// ==/UserScript==

(function () {
    'use strict';

    const VERSION = '11.0';

    // =========================================================
    // CẤU HÌNH CHUNG
    // =========================================================
    const CFG = {
        autoClick: true,        // có đáp án trong HTML -> tự tick
        aiAutoClick: false,     // đáp án AI: false = chỉ hiện trong panel, bấm "Chọn" mới tick
        autoAskAI: true,        // sau khi bấm "Bắt đầu", câu chưa có đáp án -> tự gửi Google AI
        autoAskNew: false,      // trang tải từng câu: câu mới xuất hiện sau khi bắt đầu -> tự hỏi AI (mỗi câu 1 lần)
        aiAutoPaste: true,      // tự dán đề vào Google AI + tự đọc kết quả về panel
        aiTabActive: true,      // tab Google AI hiện lên phía trước (ổn định hơn chạy nền)
        closeAITab: true,       // tự đóng tab Google AI khi có kết quả
        showNoteOnCard: true,   // hiện ghi chú đáp án dưới mỗi câu trên trang
        theme: 'auto',          // auto | dark | light
        aiUrlMaxLen: 1800,      // prompt ngắn hơn mức này thì gửi qua URL, dài hơn thì dán vào ô nhập
        aiTimeoutMs: 180000,    // chờ AI tối đa (ms)
        openOnStart: true,      // tự mở panel khi bấm "Bắt đầu"
        alwaysLauncher: true,   // nút 🤖 luôn hiện ở cửa sổ chính của mọi trang
        clickDelay: 60,
        scanDebounce: 600,      // chờ DOM yên rồi mới quét (ms)
        scanThrottle: 1500,     // tối thiểu giữa 2 lần quét (ms)
        startRegex: /(^|[^\p{L}])(bắt đầu|bat dau|start|begin|vào thi|làm bài|làm thi)/iu,
        startBtn: ''            // vd '#btnStart' nếu nút không có chữ như trên
    };

    // =========================================================
    // PROFILE THEO TRANG (ưu tiên hơn tự dò)
    // =========================================================
    const SITE_PROFILES = [
        {
            name: 'quiz-card',
            host: /./,
            selectors: {
                card: '.quiz-card',
                question: '.question-text',
                option: '.option-text',
                statement: '.statement-text',
                input: '',
                answerKey: '.answer-key'
            }
        }
        // { name: 'trang-abc', host: /abc\.vn$/, selectors: {
        //     card: '.cau-hoi', question: '.noi-dung', option: '.dap-an-item',
        //     statement: '', input: '', answerKey: '.loi-giai' } },
    ];

    // =========================================================
    // STATE
    // =========================================================
    const state = {
        items: [],              // câu đang thấy trên trang
        memory: new Map(),      // fingerprint -> item (giữ đáp án khi trang vẽ lại DOM)
        host: null, shadow: null, rootEl: null, panel: null, launcher: null,
        started: false, running: false, scanning: false, starting: false,
        mode: '', ai: null, aiStage: 0, stageFrom: 0,
        filter: 'all', tab: 'list',
        open: new Set(),        // câu đang mở phần giải thích AI
        status: { msg: 'Sẵn sàng. Bấm "Bắt đầu" hoặc "Quét lại".', kind: 'info' }
    };
    const applied = new WeakSet(); // card đã tick rồi, không tick lại

    const isTop = (() => { try { return window.top === window.self; } catch (e) { return false; } })();

    // =========================================================
    // UTILS (đọc được công thức: sup/sub/KaTeX/MathJax/MathML/alt ảnh)
    // =========================================================
    const sleep = ms => new Promise(r => setTimeout(r, ms));
    const L = i => String.fromCharCode(65 + i);

    const MATH_SEL = '.katex,mjx-container,.MathJax,.mwe-math-element,math';
    const SPECIAL_SEL = 'sup,sub,img[alt],' + MATH_SEL;
    const plainTxt = el => (el ? el.textContent || '' : '')
        .replace(/\u00a0/g, ' ').replace(/\s+/g, ' ').trim();

    function mathTex(m) {
        let t = '';
        try {
            const a = m.querySelector('annotation[encoding="application/x-tex"]') || m.querySelector('annotation');
            t = (a && a.textContent) || m.getAttribute('data-tex') || m.getAttribute('aria-label') ||
                m.getAttribute('alttext') || m.textContent || '';
        } catch (e) { t = m.textContent || ''; }
        return String(t).replace(/\s+/g, ' ').trim();
    }
    function outerMath(p) {
        let m = null;
        try { m = p.closest(MATH_SEL); } catch (e) { /* ignore */ }
        let o = m;
        while (o) { m = o; o = m.parentElement && m.parentElement.closest(MATH_SEL); }
        return m;
    }
    function richClone(el) {
        const c = el.cloneNode(true);
        c.querySelectorAll('.tm-ai-note,script,style').forEach(n => n.remove());
        c.querySelectorAll(MATH_SEL).forEach(m => m.replaceWith(document.createTextNode(' $' + mathTex(m) + '$ ')));
        c.querySelectorAll('sup').forEach(s => { const t = plainTxt(s); s.replaceWith(document.createTextNode(t ? '^' + t : '')); });
        c.querySelectorAll('sub').forEach(s => { const t = plainTxt(s); s.replaceWith(document.createTextNode(t ? '_' + t : '')); });
        c.querySelectorAll('img[alt]').forEach(i => {
            const a = (i.getAttribute('alt') || '').trim();
            i.replaceWith(document.createTextNode(a ? ` [hình: ${a}] ` : ''));
        });
        return plainTxt(c);
    }
    const txt = el => {
        if (!el) return '';
        if (el.nodeType !== 1 || !el.querySelector) return plainTxt(el);
        let has = false;
        try {
            if (el.matches(MATH_SEL)) return '$' + mathTex(el) + '$';
            has = !!el.querySelector(SPECIAL_SEL);
        } catch (e) { /* ignore */ }
        return has ? richClone(el) : plainTxt(el);
    };

    const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g,
        c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
    const norm = s => String(s || '').toLowerCase().normalize('NFC')
        .replace(/[\s\u00a0]+/g, ' ').replace(/[.,;:!?"'“”‘’()\[\]{}]/g, '').trim();
    const stripPrefix = s => String(s || '').replace(/^\s*[\(\[]?[A-Da-d][\.\)\]:]\s*/, '').trim();
    const cssEsc = s => (window.CSS && CSS.escape) ? CSS.escape(s) : String(s).replace(/["\\]/g, '\\$&');
    const INPUT_SEL = 'input[type="radio"],input[type="checkbox"]';
    const TEXT_SEL = 'input:not([type]),input[type="text"],input[type="number"],textarea';
    const OURS_SEL = '#tm-ai-root,#tm-ai-quiz-panel,#tm-ai-launcher,#tm-ai-toast';
    const clsOf = e => (e && typeof e.className === 'string' ? e.className : '');

    function hash(s) {
        let h = 5381;
        for (let i = 0; i < s.length; i++) h = ((h << 5) + h + s.charCodeAt(i)) | 0;
        return (h >>> 0).toString(36);
    }

    const isOurs = n => {
        const el = n && n.nodeType === 1 ? n : n && n.parentElement;
        return !!(el && el.closest && el.closest(OURS_SEL));
    };

    function fire(el) {
        try { el.click(); } catch (e) { /* ignore */ }
        el.dispatchEvent(new Event('input', { bubbles: true }));
        el.dispatchEvent(new Event('change', { bubbles: true }));
    }

    function copy(text) {
        try {
            if (typeof GM_setClipboard === 'function') GM_setClipboard(text);
            else if (navigator.clipboard) navigator.clipboard.writeText(text);
        } catch (e) { /* ignore */ }
    }

    function safeQ(root, sel) { try { return root.querySelector(sel); } catch (e) { return null; } }
    function safeQA(root, sel) { try { return [...root.querySelectorAll(sel)]; } catch (e) { return []; } }

    function lca(els) {
        let a = els[0];
        while (a && !els.every(e => a.contains(e))) a = a.parentElement;
        return a;
    }

    // ---------- lưu trữ (GM nếu có, không thì localStorage) ----------
    const store = {
        get(k) {
            try {
                let v = typeof GM_getValue === 'function' ? GM_getValue(k, null) : localStorage.getItem(k);
                if (typeof v === 'string') v = JSON.parse(v);
                return v;
            } catch (e) { return null; }
        },
        set(k, v) {
            try {
                if (typeof GM_setValue === 'function') GM_setValue(k, JSON.stringify(v));
                else localStorage.setItem(k, JSON.stringify(v));
            } catch (e) { /* ignore */ }
        },
        del(k) {
            try {
                if (typeof GM_deleteValue === 'function') GM_deleteValue(k);
                else localStorage.removeItem(k);
            } catch (e) { /* ignore */ }
        }
    };

    const STORE_KEY = 'tm-quiz-sel:' + location.hostname;
    const POS_KEY = 'tm-quiz-pos';
    const PANEL_POS_KEY = 'tm-quiz-panel-pos';
    const CFG_KEY = 'tm-quiz-v11-cfg';
    const OLD_CFG_KEY = 'tm-quiz-cfg';       // v5.1: chỉ lấy lại các công tắc cũ
    const CFG_FLAGS = ['autoClick', 'aiAutoClick', 'autoAskAI', 'autoAskNew', 'aiAutoPaste', 'aiTabActive', 'closeAITab', 'showNoteOnCard'];

    function loadUserSel() {
        const v = store.get(STORE_KEY);
        return v && typeof v === 'object' && v.card ? v : null;
    }
    const saveUserSel = sel => store.set(STORE_KEY, sel);
    const clearUserSel = () => store.del(STORE_KEY);

    function loadCfg() {
        const v = store.get(CFG_KEY) || store.get(OLD_CFG_KEY);
        if (!v || typeof v !== 'object') return;
        CFG_FLAGS.forEach(k => { if (typeof v[k] === 'boolean') CFG[k] = v[k]; });
        if (['auto', 'dark', 'light'].includes(v.theme)) CFG.theme = v.theme;
    }
    function saveCfg() {
        const v = { theme: CFG.theme };
        CFG_FLAGS.forEach(k => { v[k] = !!CFG[k]; });
        store.set(CFG_KEY, v);
    }

    // =========================================================
    // PARSE ĐÁP ÁN
    // =========================================================
    const LETTER_RE = /(?<![\p{L}\p{N}])([ABCD])(?![\p{L}\p{N}])/gu;
    const NUM_RE = /(?<![\p{L}\p{N}])([1-4])(?![\p{L}\p{N}])/gu;

    function answerPhrase(t) {
        t = t || '';
        const m = t.match(/(?:đáp\s*án(?:\s*đúng)?|dap\s*an|correct\s*answer|answer|đ\/a)\s*(?:là|is)?\s*[:：\-]?\s*([\s\S]+)/i);
        const s = m ? m[1] : t;
        return s.split(/giải thích|lời giải|explanation/i)[0].trim();
    }

    function resolveMC(it, keyText) {
        const phrase = answerPhrase(keyText);
        if (!phrase) return null;
        const n = it.options.length;
        const cleaned = norm(phrase);

        if (cleaned.length > 3) {
            let idx = it.options.findIndex(o => norm(o.text) === cleaned);
            if (idx >= 0) return L(idx);
            const pm = phrase.match(/^\s*[\(\[]?([A-D])[\.\)\]:]\s*\S/i);
            if (pm) return pm[1].toUpperCase();
            idx = it.options.findIndex(o => {
                const t = norm(o.text);
                return t.length >= 3 && (cleaned.includes(t) || t.includes(cleaned));
            });
            if (idx >= 0) return L(idx);
        }
        const letters = [...phrase.toUpperCase().matchAll(LETTER_RE)]
            .map(m => m[1]).filter(c => c.charCodeAt(0) - 65 < n);
        if (letters.length) return it.multi ? [...new Set(letters)].join('') : letters[0];
        const nums = [...phrase.matchAll(NUM_RE)].map(m => L(Number(m[1]) - 1))
            .filter(c => c.charCodeAt(0) - 65 < n);
        if (nums.length) return it.multi ? [...new Set(nums)].join('') : nums[0];
        return null;
    }

    const TRUE_RE = /^(đúng|true|đ|t|yes|có)$/i;
    const isTrueText = t => TRUE_RE.test(norm(t));
    const TF_TEXT_RE = /^(đúng|sai|true|false|đ|s|t|f)$/i;
    const TF_ITEM_RE = /(?<![\p{L}\p{N}])[a-d]\s*[):=.-]\s*(đúng|sai|true|false|đ|s|t|f)(?![\p{L}\p{N}])/iu;
    const TF_SEQ_RE = /^(?:\s*(?:đúng|sai|true|false|đ|s)\s*[,;/]?\s*){2,}$/iu;

    function parseTF(t, n) {
        if (!t) return null;
        const res = {};
        const re = /(?<![\p{L}\p{N}])([a-d])\s*[):=.-]\s*(đúng|sai|true|false|đ|s|t|f)(?![\p{L}\p{N}])/giu;
        let m;
        while ((m = re.exec(t))) res[m[1].toLowerCase()] = /^(đúng|true|đ|t)$/i.test(m[2]);
        if (Object.keys(res).length) return res;
        if (n) {
            const seqRe = TF_SEQ_RE.test(t)
                ? /(?<![\p{L}\p{N}])(đúng|sai|true|false|đ|s)(?![\p{L}\p{N}])/giu
                : /(?<![\p{L}\p{N}])(đúng|sai|true|false)(?![\p{L}\p{N}])/giu;
            const toks = [...t.matchAll(seqRe)].map(x => /^(đúng|true|đ)$/i.test(x[1]));
            if (toks.length === n) {
                toks.forEach((v, i) => { res[String.fromCharCode(97 + i)] = v; });
                return res;
            }
        }
        return null;
    }

    function fmtAnswer(it) {
        if (it.answer == null) return '';
        if (it.type === 'mc') return String(it.answer).split('').join(', ');
        if (it.type === 'sa') return String(it.answer);
        return Object.entries(it.answer).map(([k, v]) => `${k}: ${v ? 'Đúng' : 'Sai'}`).join(' · ');
    }

    // ----- câu điền đáp án ngắn -----
    const cleanAnswer = s => String(s || '').replace(/\s+/g, ' ').trim()
        .replace(/^["“”'‘’`]+|["“”'‘’`]+$/g, '').replace(/[.。]+$/, '').trim();

    function saFromKey(it) {
        let p = cleanAnswer(answerPhrase(it.key));
        if (!p || p.length > 200) return null;
        if (it.blanks.length === 1) p = cleanAnswer(p.split(/\s*\|\s*/)[0]);
        else p = p.split(/\s*[;|]\s*/).map(x => x.replace(/^\(?\d+[).:]\s*/, '')).join('; ');
        return p || null;
    }

    // đáp án ghi sẵn trên chính ô nhập (data-answer, data-correct-answer...)
    function saMarked(it) {
        const vals = it.blanks.map(b => {
            for (const a of ['data-correct-answer', 'data-answer', 'data-correct', 'data-key', 'data-solution']) {
                const v = b.getAttribute && b.getAttribute(a);
                if (v && !/^(true|false|1|0|yes|no)$/i.test(v.trim())) return v.trim();
            }
            return '';
        });
        return vals.length && vals.every(Boolean) ? vals.join('; ') : '';
    }

    // =========================================================
    // TÌM ĐÁP ÁN TRONG HTML
    // =========================================================
    const KEY_SEL = [
        '.answer-key', '[class*="answer-key" i]', '[class*="answerkey" i]',
        '[class*="correct-answer" i]', '[class*="right-answer" i]',
        '[class*="dap-an" i]', '[class*="dapan" i]', '[class*="solution" i]',
        '[data-answer]', '[data-correct-answer]', '[data-correct-option]'
    ].join(',');

    const KEY_TEXT_RE = /^\s*(đáp án đúng|đáp án|dap an|đ\/a|correct answer|answer|correct)\s*[:：\-]/i;
    const CORRECT_RE = /(^|[\s_-])(correct|right|is-correct|true-answer|answer-correct)($|[\s_-])/i;
    const WRONG_RE = /(in|not|un)[-_]?correct|wrong|false/i;

    function hasCorrect(...els) {
        for (const e of els) {
            if (!e || !e.getAttribute) continue;
            for (const a of ['data-correct', 'data-is-correct', 'data-right', 'data-iscorrect']) {
                const v = e.getAttribute(a);
                if (v !== null && /^(true|1|yes|correct)$/i.test(v)) return true;
            }
            const c = clsOf(e);
            if (CORRECT_RE.test(c) && !WRONG_RE.test(c)) return true;
        }
        return false;
    }

    function findKey(card, extraSel) {
        let el = extraSel ? safeQ(card, extraSel) : null;
        if (!el) el = safeQA(card, KEY_SEL).find(e => !isOurs(e) && !e.closest('.tm-ai-note')) || null;
        if (el) {
            const t = txt(el) || el.getAttribute('data-answer') ||
                el.getAttribute('data-correct-answer') || el.getAttribute('data-correct-option') || '';
            if (t) return t;
        }
        const ds = card.dataset || {};
        const d = ds.answer || ds.correctAnswer || ds.correct || ds.correctOption;
        if (d) return String(d);
        for (const e of card.querySelectorAll('*')) {
            if (e.children.length > 1 || isOurs(e) || e.closest('.tm-ai-note')) continue;
            const t = txt(e);
            if (t.length <= 160 && KEY_TEXT_RE.test(t)) return t;
        }
        return null;
    }

    // giữ nguyên chỉ số trên/dưới và công thức (x^2, H_2SO_4, $\frac{a}{b}$)
    function textExcluding(root, excludes) {
        const pieces = [];
        const doneMath = new Set();
        let prevScript = false;
        const w = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
            acceptNode(n) {
                const p = n.parentElement;
                if (!p) return NodeFilter.FILTER_REJECT;
                if (p.closest('script,style,noscript,.tm-ai-note,#tm-ai-root')) return NodeFilter.FILTER_REJECT;
                try {
                    const k = p.closest(KEY_SEL);
                    if (k && k !== root && root.contains(k)) return NodeFilter.FILTER_REJECT;
                } catch (e) { /* ignore */ }
                const pt = txt(p);
                if (pt.length <= 160 && KEY_TEXT_RE.test(pt)) return NodeFilter.FILTER_REJECT;
                for (const e of excludes) if (e && e.contains(n)) return NodeFilter.FILTER_REJECT;
                const m = outerMath(p);
                if (m && root.contains(m)) {
                    if (!doneMath.has(m)) { doneMath.add(m); pieces.push({ t: '$' + mathTex(m) + '$', glue: false }); }
                    return NodeFilter.FILTER_REJECT;
                }
                return NodeFilter.FILTER_ACCEPT;
            }
        });
        let n;
        while ((n = w.nextNode())) {
            const p = n.parentElement;
            const sc = p.closest('sup') ? '^' : p.closest('sub') ? '_' : '';
            const v = n.nodeValue.replace(/\u00a0/g, ' ');
            const t = v.replace(/\s+/g, ' ');
            if (sc) pieces.push({ t: sc + t.trim(), glue: true });
            else pieces.push({ t, glue: prevScript && !/^\s/.test(v) });
            prevScript = !!sc;
        }
        let s = '';
        for (const x of pieces) {
            const t = x.t.trim();
            if (!t) continue;
            s += (x.glue || !s ? '' : ' ') + t;
        }
        s = s.replace(/\s+/g, ' ').trim();
        s = s.replace(/(\s+[A-D]){2,}\s*$/, '').trim();
        return s.slice(0, 1500);
    }

    // câu có hình mà AI không nhìn thấy được (để cảnh báo)
    function hasUnseenImage(it) {
        return safeQA(it.card, 'img,canvas,svg').some(im => {
            if (isOurs(im) || im.closest('.tm-ai-note')) return false;
            try { if (im.closest(MATH_SEL)) return false; } catch (e) { /* ignore */ }
            const r = im.getBoundingClientRect();
            if (r.width < 40 || r.height < 40) return false;
            if (im.tagName === 'IMG' && (im.getAttribute('alt') || '').trim().length >= 3) return false;
            return true;
        });
    }

    // =========================================================
    // DỰNG ĐỐI TƯỢNG OPTION / ITEM
    // =========================================================
    function inputNear(el) {
        if (el.matches && el.matches(INPUT_SEL)) return el;
        let n = el;
        for (let i = 0; i < 3 && n; i++, n = n.parentElement) {
            const inputs = n.querySelectorAll ? n.querySelectorAll(INPUT_SEL) : [];
            if (inputs.length === 1) return inputs[0];
            if (inputs.length > 1) break;
        }
        return null;
    }

    function optFromEl(el, i) {
        const input = inputNear(el);
        return {
            letter: L(i), text: stripPrefix(txt(el)), el, input, ex: [el],
            correct: hasCorrect(el, input, el.closest && el.closest('label,li'))
        };
    }

    function containerOf(input) {
        const lab = (input.labels && input.labels[0]) || input.closest('label') ||
            (input.id && document.querySelector(`label[for="${cssEsc(input.id)}"]`));
        if (lab) return lab;
        const p = input.parentElement;
        if (p && p.querySelectorAll(INPUT_SEL).length === 1) return p;
        return input;
    }

    function optFromInput(input, i) {
        const el = containerOf(input);
        let t = el === input ? txt(input.nextSibling) : txt(el);
        if (!t && el !== input) t = txt(el.nextElementSibling);
        return {
            letter: L(i), text: stripPrefix(t), el, input,
            ex: el === input ? [input, input.nextSibling] : [el],
            correct: hasCorrect(input, el, el.parentElement)
        };
    }

    const base = () => ({ solved: false, answer: null, source: null, aiText: '', asked: false, hasImg: false });

    function makeMC(card, options, question, keySel) {
        const multi = options.some(o => o.input && o.input.type === 'checkbox');
        const marked = options.filter(o => o.correct).map(o => o.letter);
        return Object.assign(base(), {
            type: 'mc', card, question, options, multi,
            key: findKey(card, keySel),
            marked: marked.length && marked.length < options.length ? marked.join('') : ''
        });
    }

    function makeTF(card, statements, question, keySel) {
        const item = Object.assign(base(), {
            type: 'tf', card, question, statements,
            key: findKey(card, keySel), markedTF: null
        });
        const mk = {};
        let all = statements.length > 0;
        for (const st of statements) {
            const c = st.opts && st.opts.find(o => o.correct);
            if (c) mk[st.letter] = isTrueText(c.text); else all = false;
        }
        if (all) item.markedTF = mk;
        return item;
    }

    function makeSA(card, blanks, question, keySel) {
        return Object.assign(base(), { type: 'sa', card, question, blanks, key: findKey(card, keySel) });
    }

    // =========================================================
    // CÁCH 1 + 2: SELECTOR (người dùng lưu / profile theo trang)
    // =========================================================
    function fromSelectors(sel) {
        if (!sel || !sel.card) return [];
        const out = [];
        for (const card of safeQA(document, sel.card)) {
            if (isOurs(card)) continue;
            const qEl = sel.question ? safeQ(card, sel.question) : null;

            const optEls = sel.option ? safeQA(card, sel.option) : [];
            if (optEls.length >= 2) {
                const options = optEls.map(optFromEl);
                const q = qEl ? txt(qEl) : textExcluding(card, options.flatMap(o => o.ex));
                out.push(makeMC(card, options, q, sel.answerKey));
                continue;
            }
            const stEls = sel.statement ? safeQA(card, sel.statement) : [];
            if (stEls.length) {
                const statements = stEls.map((el, i) => ({
                    letter: String.fromCharCode(97 + i), text: txt(el), el
                }));
                out.push(makeTF(card, statements, qEl ? txt(qEl) : '', sel.answerKey));
                continue;
            }
            const inEls = safeQA(card, sel.input || TEXT_SEL).filter(e => !isOurs(e) && !e.disabled);
            if (inEls.length) {
                out.push(makeSA(card, inEls, qEl ? txt(qEl) : textExcluding(card, inEls), sel.answerKey));
            }
        }
        return out;
    }

    // =========================================================
    // CÁCH 3: TỰ DÒ THEO radio / checkbox
    // =========================================================
    function splitGroup(inputs) {
        if (inputs.length <= 8) return [inputs];
        const root = lca(inputs);
        if (!root) return [inputs];
        const parts = [...root.children].map(c => inputs.filter(i => c.contains(i))).filter(a => a.length);
        if (parts.length < 2 || !parts.some(p => p.length >= 2)) return [inputs];
        return parts.flatMap(p => (p.length >= 2 ? splitGroup(p) : []));
    }

    function climbFrom(start, mine, allInputs) {
        let el = start;
        while (el.parentElement) {
            const p = el.parentElement;
            if (p === document.body || p === document.documentElement || p.matches('main,form')) break;
            if (allInputs.some(i => !mine.has(i) && p.contains(i))) break;
            if (p.textContent.length > 5000) break;
            el = p;
        }
        return el;
    }

    function climbCard(group, allInputs) {
        const el = lca(group);
        if (!el) return null;
        const mine = new Set(group);
        // ô text nằm ngay trong khối đáp án (vd "Khác: ___") thuộc về câu này
        allInputs.forEach(i => {
            if (!mine.has(i) && i.matches && i.matches(TEXT_SEL) && el.contains(i)) mine.add(i);
        });
        return climbFrom(el, mine, allInputs);
    }

    function fromInputs() {
        const all = [...document.querySelectorAll(INPUT_SEL)]
            .filter(i => !isOurs(i) && !i.closest('nav,header,footer,aside'));
        if (all.length < 2) return [];

        let uid = 0;
        const ids = new WeakMap();
        const idOf = el => { if (!ids.has(el)) ids.set(el, ++uid); return ids.get(el); };
        const map = new Map();
        for (const i of all) {
            const holder = i.closest('fieldset,ul,ol,dl') || (i.parentElement && i.parentElement.parentElement) || i.parentElement;
            const k = i.type + '|' + (i.name || ('~' + (holder ? idOf(holder) : 0)));
            if (!map.has(k)) map.set(k, []);
            map.get(k).push(i);
        }
        const groups = [...map.values()].flatMap(splitGroup).filter(g => g.length >= 2);
        // ô điền ngắn cũng chặn việc leo lên thẻ cha, để câu trắc nghiệm không nuốt câu điền
        const texts = safeQA(document, TEXT_SEL).filter(e => !isOurs(e));
        const flat = groups.flat().concat(texts);

        const rows = groups.map(g => {
            const options = g.map(optFromInput);
            const card = climbCard(g, flat);
            const isTF = options.length === 2 && options.every(o => TF_TEXT_RE.test(norm(o.text)));
            return { g, options, card, isTF };
        }).filter(r => r.card);

        const out = [];
        const tfClusters = new Map();

        for (const r of rows) {
            if (r.isTF) {
                const par = r.card.parentElement;
                if (!tfClusters.has(par)) tfClusters.set(par, []);
                tfClusters.get(par).push(r);
                continue;
            }
            const q = textExcluding(r.card, r.options.flatMap(o => o.ex));
            const item = makeMC(r.card, r.options, q, '');
            if (q || item.key || item.marked) out.push(item);
        }

        for (const [par, list] of tfClusters) {
            if (list.length >= 2 && par) {
                const statements = list.map((r, i) => ({
                    letter: String.fromCharCode(97 + i),
                    text: textExcluding(r.card, r.options.flatMap(o => o.ex)),
                    el: r.card, opts: r.options
                }));
                const mine = new Set(list.flatMap(r => r.g));
                const card = climbFrom(par, mine, flat);
                const q = textExcluding(card, list.map(r => r.card));
                out.push(makeTF(card, statements, q, ''));
            } else {
                for (const r of list) {
                    const q = textExcluding(r.card, r.options.flatMap(o => o.ex));
                    const item = makeMC(r.card, r.options, q, '');
                    if (q || item.key || item.marked) out.push(item);
                }
            }
        }
        return out;
    }

    // =========================================================
    // CÁCH 4: ARIA (role=radiogroup / radio / checkbox / option)
    // =========================================================
    function fromAria() {
        const OPT = '[role="radio"],[role="checkbox"],[role="option"]';
        const groups = safeQA(document, '[role="radiogroup"],[role="group"],[role="listbox"]')
            .filter(g => !isOurs(g))
            .map(g => ({ g, opts: safeQA(g, OPT).filter(e => txt(e)) }))
            .filter(x => x.opts.length >= 2 && x.opts.length <= 8);
        if (!groups.length) return [];
        const flat = groups.flatMap(x => x.opts);
        return groups.map(({ g, opts }) => {
            const options = opts.map(optFromEl);
            const card = climbFrom(g, new Set(opts), flat);
            const q = textExcluding(card, opts);
            const it = makeMC(card, options, q, '');
            it.multi = opts.some(e => e.getAttribute('role') === 'checkbox');
            return it;
        }).filter(it => it.question || it.key || it.marked);
    }

    // =========================================================
    // CÁCH 5: TỰ DÒ THEO TÊN CLASS / data-attribute (div thay input)
    // =========================================================
    function fromClassNames() {
        const OPT_SEL = '[class*="option" i],[class*="choice" i],[class*="answer" i],[class*="dap-an" i]';
        const BAD = /answer-?key|correct-?answer|right-?answer|solution|explain|result|feedback|tm-ai/i;

        const leafOpts = q => {
            const m = safeQA(q, OPT_SEL).filter(e =>
                !isOurs(e) && !BAD.test(clsOf(e)) && txt(e));
            return m.filter(e => !m.some(o => o !== e && e.contains(o)));
        };

        let cands = safeQA(document,
            '[class*="question" i],[class*="cau-hoi" i],[class*="quiz-item" i],[data-question],[data-question-id],[data-qid]')
            .filter(e => !isOurs(e))
            .map(q => ({ q, opts: leafOpts(q) }))
            .filter(c => c.opts.length >= 2 && c.opts.length <= 8);

        cands = cands.filter(c => !cands.some(o =>
            o !== c && o.q.contains(c.q) && o.opts.length === c.opts.length && o.opts[0] === c.opts[0]));
        cands = cands.filter(c => {
            const inner = cands.filter(o => o !== c && c.q.contains(o.q));
            return new Set(inner.map(o => o.opts[0])).size < 2;
        });

        return cands.map(({ q, opts }) => {
            const options = opts.map(optFromEl);
            const ex = opts.map(e => e.closest('li,label,tr') || e);
            const question = textExcluding(q, ex);
            return makeMC(q, options, question, '');
        }).filter(it => it.question || it.key || it.marked);
    }

    // =========================================================
    // CÁCH 6: TỰ DÒ THEO CHỮ "A. ..., B. ..., C. ..., D. ..." (quét sâu)
    // =========================================================
    function fromLabeledText() {
        const PFX = /^\s*[\(\[]?([A-Da-d])[\.\)\]:]\s*\S/;
        let labs = safeQA(document.body, 'li,p,div,span,label,td,dd,button,a')
            .filter(e => !isOurs(e) && !e.closest('nav,header,footer,aside'))
            .filter(e => { const t = txt(e); return t.length >= 2 && t.length <= 300 && PFX.test(t); });
        labs = labs.filter(e => !labs.some(o => o !== e && e.contains(o)));
        if (labs.length < 2) return [];

        const slotOf = (e, d) => { let n = e; for (let i = 0; i < d && n.parentElement; i++) n = n.parentElement; return n; };
        const used = new WeakSet();
        const found = [];

        for (let d = 0; d <= 2; d++) {
            const byPar = new Map();
            for (const e of labs) {
                if (used.has(e)) continue;
                const slot = slotOf(e, d);
                const par = slot.parentElement;
                if (!par || par === document.body) continue;
                if (!byPar.has(par)) byPar.set(par, []);
                byPar.get(par).push({ e, slot, letter: txt(e).match(PFX)[1].toUpperCase() });
            }
            for (const [par, arr] of byPar) {
                let cur = [];
                const flush = () => {
                    if (cur.length >= 2) {
                        cur.forEach(o => used.add(o.e));
                        found.push({ par, run: cur });
                    }
                };
                const seenSlots = new Set();
                for (const o of arr) {
                    if (seenSlots.has(o.slot)) continue;
                    seenSlots.add(o.slot);
                    if (o.letter === L(cur.length)) cur.push(o);
                    else { flush(); cur = o.letter === 'A' ? [o] : []; }
                }
                flush();
            }
        }
        if (!found.length) return [];

        const allSlots = found.flatMap(f => f.run.map(o => o.slot));
        const out = [];
        for (const f of found) {
            const slots = f.run.map(o => o.slot);
            const card = climbFrom(f.par, new Set(slots), allSlots);
            const question = textExcluding(card, slots);
            if (question.length < 4) continue;
            out.push(makeMC(card, slots.map(optFromEl), question, ''));
        }
        return out;
    }

    // =========================================================
    // CÁCH 7: CÂU ĐIỀN ĐÁP ÁN NGẮN (ô nhập text / number / textarea)
    // =========================================================
    const NOT_QUIZ_FIELD = /search|tìm kiếm|tim kiem|e-?mail|user(name)?|login|đăng nhập|pass(word)?|captcha|otp|phone|điện thoại|coupon|mã giảm|newsletter|subscribe|comment|bình luận|họ tên|full ?name|address|địa chỉ/i;
    const QCTX_RE = /question|cau-?hoi|quiz|exam|bai-?tap|blank|fill/i;
    const QNUM_RE = /(^|[^\p{L}\p{N}])(câu|question|bài|q)\s*\.?\s*\d+/iu;

    function fromTextInputs(existing) {
        const ctrls = [...document.querySelectorAll('input,textarea')]
            .filter(e => !isOurs(e) && !e.closest('nav,header,footer,aside,form[role="search"]'));
        const texts = ctrls.filter(e => {
            if (e.disabled || e.readOnly) return false;
            if (e.tagName === 'INPUT' && !/^(text|number)?$/i.test(e.getAttribute('type') || '')) return false;
            const meta = [e.name, e.id, e.placeholder, e.getAttribute('aria-label'), e.getAttribute('autocomplete')].join(' ');
            return !NOT_QUIZ_FIELD.test(meta);
        });
        if (!texts.length) return [];

        const hasOther = existing.length > 0;
        const cards = existing.map(i => i.card);
        const byCard = new Map();
        const out = [];

        for (const t of texts) {
            if (cards.some(c => c.contains(t))) continue; // ô "Khác: ..." nằm trong câu trắc nghiệm
            let card = climbFrom(t, new Set([t]), ctrls);
            if (card === t) card = t.parentElement || t; // nhiều ô nằm chung một dòng -> gộp thành 1 câu
            if (!card || card === document.body || card === document.documentElement) continue;
            if (cards.some(c => card.contains(c))) continue;
            if (byCard.has(card)) { byCard.get(card).blanks.push(t); continue; }
            if (txt(card).length > 1800) continue;

            const question = textExcluding(card, [t]);
            const key = findKey(card, '');
            const ctx = hasOther || key ||
                QCTX_RE.test(clsOf(card) + ' ' + card.id + ' ' + clsOf(card.parentElement)) ||
                QNUM_RE.test(question.slice(0, 120)) ||
                !!saMarked({ blanks: [t] });
            if (!ctx) continue;
            if (question.length < 4 && !key) continue;

            const it = makeSA(card, [t], question, '');
            byCard.set(card, it);
            out.push(it);
        }
        return out;
    }

    // =========================================================
    // GỘP TẤT CẢ CÁCH DÒ + CHỐNG TRÙNG
    // =========================================================
    function fpOf(it) {
        const b = it.type === 'mc'
            ? it.options.map(o => norm(o.text)).join('|')
            : it.type === 'sa'
                ? 'blanks' + it.blanks.length
                : it.statements.map(s => norm(s.text)).join('|');
        return it.type + ':' + hash(norm(it.question).slice(0, 400) + '||' + b);
    }

    function firstEl(it) {
        const f = it.type === 'mc' ? it.options[0] : it.type === 'tf' ? it.statements[0] : null;
        return f ? f.el : (it.type === 'sa' ? it.blanks[0] : null);
    }

    function postprocess(items) {
        // 1. cùng một đáp án đầu tiên -> giữ thẻ ngoài cùng (để tìm key tốt hơn)
        const byEl = new Map();
        for (const it of items) {
            const k = firstEl(it);
            if (!k) { byEl.set(Symbol('x'), it); continue; }
            const old = byEl.get(k);
            if (!old) byEl.set(k, it);
            else if (it.card !== old.card && it.card.contains(old.card)) byEl.set(k, it);
        }
        let list = [...byEl.values()];
        // 2. bỏ thẻ "bọc" chứa từ 2 câu trở lên
        list = list.filter(a => list.filter(b => b !== a && a.card.contains(b.card)).length < 2);
        // 3. bỏ bản sao cùng nội dung (vd bản mobile/desktop ẩn), giữ bản đầu
        const seen = new Map();
        const out = [];
        for (const it of list) {
            it.fp = fpOf(it);
            const n = seen.get(it.fp) || 0;
            if (n && it.question.length > 5) continue;
            seen.set(it.fp, n + 1);
            if (n) it.fp += '#' + n;
            out.push(it);
        }
        return out;
    }

    function detectItems(deep) {
        const tries = [];
        const user = loadUserSel();
        if (user) tries.push(['selector tuỳ chỉnh', () => fromSelectors(user)]);
        for (const p of SITE_PROFILES) {
            if (p.host.test(location.hostname)) tries.push([`profile: ${p.name}`, () => fromSelectors(p.selectors)]);
        }
        tries.push(['tự dò radio/checkbox', fromInputs]);
        tries.push(['tự dò ARIA', fromAria]);
        tries.push(['tự dò theo class', fromClassNames]);
        if (deep) tries.push(['tự dò theo chữ A/B/C/D', fromLabeledText]);

        let items = [], mode = '';
        for (const [m, fn] of tries) {
            let r = [];
            try { r = fn(); } catch (e) { console.warn('[AI Quiz]', m, e); }
            if (r.length) { items = r; mode = m; break; }
        }
        try {
            const extra = fromTextInputs(items);
            if (extra.length) {
                items = items.concat(extra);
                mode = mode ? mode + ' + ô điền ngắn' : 'tự dò ô điền ngắn';
            }
        } catch (e) { console.warn('[AI Quiz] ô điền ngắn', e); }
        if (!items.length) return { items: [], mode: '' };
        items.sort((a, b) => a.card === b.card ? 0 :
            (a.card.compareDocumentPosition(b.card) & Node.DOCUMENT_POSITION_FOLLOWING ? -1 : 1));
        items = postprocess(items);
        return items.length ? { items, mode } : { items: [], mode: '' };
    }

    // Giữ đáp án theo fingerprint: trang vẽ lại DOM thì gắn lại vào phần tử mới
    function reconcile(found) {
        return found.map((it, idx) => {
            const old = state.memory.get(it.fp);
            let res = it;
            if (old && old.type === it.type) {
                Object.assign(old, {
                    card: it.card, question: it.question, options: it.options,
                    statements: it.statements, blanks: it.blanks, multi: it.multi,
                    marked: it.marked, markedTF: it.markedTF
                });
                if (it.key) old.key = it.key;
                res = old;
            } else {
                state.memory.set(it.fp, it);
            }
            res.index = idx;
            return res;
        });
    }

    function scan(deep) {
        if (state.scanning) return state.items.length > 0;
        state.scanning = true;
        try {
            const { items, mode } = detectItems(deep !== false);
            state.items = reconcile(items);
            state.mode = mode;
        } finally {
            state.scanning = false;
        }
        render();
        return state.items.length > 0;
    }

    // =========================================================
    // CLICK / ĐIỀN
    // =========================================================
    // lựa chọn dạng div: nếu trang đã đánh dấu "đang chọn" thì không bấm lại (tránh bỏ chọn)
    const SELECTED_CLS = /(^|[\s_-])(selected|active|checked|chosen|is-selected|is-active|is-checked)($|[\s_-])/i;
    const OUR_CLS = /\btm-ai-(picked|flash)\b/g;
    function isOn(el) {
        for (const e of [el, el.closest && el.closest('label,li')]) {
            if (!e) continue;
            if (e.getAttribute('aria-checked') === 'true' || e.getAttribute('aria-selected') === 'true') return true;
            if (SELECTED_CLS.test(clsOf(e).replace(OUR_CLS, ''))) return true;
        }
        return false;
    }

    function setNativeValue(el, v) {
        el.focus();
        const proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
        const d = Object.getOwnPropertyDescriptor(proto, 'value');
        if (d && d.set) d.set.call(el, v); else el.value = v;
        el.dispatchEvent(new Event('input', { bubbles: true }));
        el.dispatchEvent(new Event('change', { bubbles: true }));
        el.dispatchEvent(new KeyboardEvent('keyup', { bubbles: true }));
    }

    async function fillSA(it, answer) {
        const parts = it.blanks.length > 1 ? String(answer).split(/\s*[;|]\s*/) : [String(answer)];
        for (let i = 0; i < it.blanks.length; i++) {
            const v = parts[i];
            if (!v) continue;
            const b = it.blanks[i];
            b.classList.add('tm-ai-picked');
            if (b.value !== v) setNativeValue(b, v);
            await sleep(CFG.clickDelay);
        }
    }

    async function clickOption(opt) {
        if (!opt) return;
        const inp = opt.input;
        if (inp) {
            if (!inp.checked) fire(inp);
            if (!inp.checked) fire(opt.el);
        } else if (!isOn(opt.el)) {
            fire(opt.el);
        }
        (opt.el.closest('label,li') || opt.el).classList.add('tm-ai-picked');
        await sleep(CFG.clickDelay);
    }

    async function clickMC(it, letters) {
        for (const ch of String(letters)) {
            const opt = it.options[ch.charCodeAt(0) - 65];
            if (opt) await clickOption(opt);
        }
    }

    function tfControls(stEl) {
        let n = stEl;
        for (let i = 0; i < 5 && n; i++, n = n.parentElement) {
            const radios = [...n.querySelectorAll('input[type="radio"]')];
            if (radios.length >= 2) return { radios };
            const btns = [...n.querySelectorAll('button, label')]
                .filter(b => /^(đúng|sai|true|false|đ|s)$/i.test(txt(b)));
            if (btns.length >= 2) return { btns };
        }
        return null;
    }

    async function clickTF(it, answers) {
        for (const st of it.statements) {
            const val = answers && answers[st.letter];
            if (typeof val !== 'boolean') continue;

            if (st.opts) {
                const opt = st.opts.find(o => isTrueText(o.text) === val);
                if (opt) await clickOption(opt);
                continue;
            }
            const c = tfControls(st.el);
            if (!c) continue;
            let target;
            if (c.radios) {
                const yes = ['true', '1', 'đúng', 'dung', 't', 'd'];
                const no = ['false', '0', 'sai', 'f', 's'];
                target = c.radios.find(r => (val ? yes : no).includes(String(r.value).toLowerCase()))
                    || c.radios[val ? 0 : 1];
            } else {
                target = c.btns.find(b => (val ? /đúng|true|^đ$/i : /sai|false|^s$/i).test(txt(b)))
                    || c.btns[val ? 0 : 1];
            }
            if (target) {
                fire(target);
                (target.closest('label') || target).classList.add('tm-ai-picked');
            }
            await sleep(CFG.clickDelay);
        }
    }

    async function pick(it) {
        if (it.answer == null || it.answer === '') return;
        if (it.type === 'mc') await clickMC(it, it.answer);
        else if (it.type === 'tf') await clickTF(it, it.answer);
        else await fillSA(it, it.answer);
        applied.add(it.card);
    }

    // =========================================================
    // GIẢI TỪ ĐÁP ÁN CÓ SẴN TRONG HTML
    // =========================================================
    function cardNote(it) {
        if (!CFG.showNoteOnCard || !it.noteHtml) return;
        let box = it.card.querySelector(':scope > .tm-ai-note');
        if (!box) {
            box = document.createElement('div');
            box.className = 'tm-ai-note';
            it.card.appendChild(box);
        }
        if (box.innerHTML !== it.noteHtml) box.innerHTML = it.noteHtml;
    }

    function aiNote(it) {
        const extra = String(it.aiText || '').split('\n').slice(1).join(' ').replace(/\s+/g, ' ').trim().slice(0, 260);
        return `🤖 <b>${esc(fmtAnswer(it))}</b>${extra ? `<div>${esc(extra)}</div>` : ''}`;
    }

    async function solveFromKey(it) {
        if (it.solved) return false;
        let ans = null;
        if (it.type === 'mc') {
            if (it.key) ans = resolveMC(it, it.key);
            if (!ans && it.marked) ans = it.marked;
            if (ans && !it.multi) ans = ans[0];
        } else if (it.type === 'sa') {
            if (it.key) ans = saFromKey(it);
            if (!ans) ans = saMarked(it) || null;
        } else {
            if (it.key) ans = parseTF(it.key, it.statements.length);
            if (!ans && it.markedTF) ans = it.markedTF;
        }
        if (!ans) return false;

        it.answer = ans; it.solved = true; it.source = 'answer-key';
        it.noteHtml = `✓ <b>${esc(fmtAnswer(it))}</b>${it.key ? `<div>${esc(it.key)}</div>` : ''}`;
        if (CFG.autoClick) await pick(it);
        cardNote(it);
        return true;
    }

    // câu đã giải nhưng trang vừa vẽ lại DOM -> tick/ghi chú lại một lần
    async function reapply(it) {
        if (!it.solved || applied.has(it.card)) return;
        const should = (it.source === 'answer-key' && CFG.autoClick) ||
            (it.source === 'google-ai' && CFG.aiAutoClick);
        if (should) await pick(it);
        if (it.source === 'answer-key' || it.source === 'google-ai') cardNote(it);
    }

    async function solveAllByKey() {
        if (state.running) return;
        state.running = true;
        try {
            for (const it of state.items) {
                if (!it.solved) await solveFromKey(it);
                else await reapply(it);
            }
        } finally {
            state.running = false;
        }
        render();
    }

    // =========================================================
    // GOOGLE AI (luồng tự động của v5.1)
    // Đáp án có sẵn trong HTML KHÔNG được gửi đi.
    // Tab quiz và tab Google nói chuyện với nhau qua GM_setValue/GM_getValue.
    // =========================================================
    const JOB_KEY = 'tm-quiz11-job';
    const RESULT_KEY = 'tm-quiz11-result';
    const canCrossTab = () => typeof GM_setValue === 'function' && typeof GM_getValue === 'function';

    // ---------- Prompt ngắn, tự nhiên ----------
    function buildPrompt(list, token) {
        const fmts = [];
        if (list.some(i => i.type === 'mc' && !i.multi)) fmts.push('"3: B"');
        if (list.some(i => i.type === 'mc' && i.multi)) fmts.push('"4: A, C" (câu chọn nhiều đáp án)');
        if (list.some(i => i.type === 'tf')) fmts.push('"5: a=Đúng, b=Sai, c=Đúng, d=Sai"');
        if (list.some(i => i.type === 'sa')) fmts.push('"6: 25" (câu điền đáp án ngắn: chỉ ghi đáp án, nhiều chỗ trống thì ngăn cách bằng dấu ;)');

        const head = `Giải giúp mình các câu sau. Chỉ trả về đáp án, mỗi câu đúng 1 dòng theo dạng ${fmts.join(' hoặc ')}, ` +
            'không giải thích, không lời dẫn, không bảng, không thêm nội dung khác. ' +
            'Công thức viết dạng chữ: x^2 là x mũ 2, H_2O là H₂O, $...$ là LaTeX.';

        const body = list.map(it => {
            const n = it.index + 1;
            it.hasImg = hasUnseenImage(it);
            const img = it.hasImg ? ' [câu có hình minh hoạ mà mình không gửi được, nếu cần hình thì cứ chọn đáp án khả dĩ nhất]' : '';
            if (it.type === 'mc') {
                return `Câu ${n}${it.multi ? ' (chọn nhiều)' : ''}: ${it.question}${img}\n` +
                    it.options.map(o => `${o.letter}. ${o.text}`).join('\n');
            }
            if (it.type === 'sa') {
                return `Câu ${n} (điền đáp án ngắn${it.blanks.length > 1 ? ', ' + it.blanks.length + ' chỗ trống, cách nhau dấu ;' : ''}): ${it.question}${img}`;
            }
            return `Câu ${n} (Đúng/Sai): ${it.question}${img}\n` +
                it.statements.map(s => `${s.letter}) ${s.text}`).join('\n');
        }).join('\n\n');

        return head + '\n\n' + body + (token ? '\n\n' + token : '');
    }

    // ---------- Đọc kết quả AI: nhiều kiểu viết ----------
    const cleanLine = l => String(l || '').replace(/\*\*|__|`+/g, '').replace(/^\s*[#>]+\s*/, '')
        .replace(/^\s*[-•·*]\s*/, '').replace(/\s+/g, ' ').trim().replace(/[*_]+$/, '').replace(/^_+/, '');
    const RESULT_STRICT = /^(?:đáp án\s*(?:của\s*)?)?(?:(?:câu|question|q|bài)\s*)?\.?\s*(\d{1,3})\s*[:：\-–—.)=]\s*(.+)$/iu;
    const RESULT_LOOSE = /^(?:đáp án\s*(?:của\s*)?)?(?:câu|question|q|bài)\s*\.?\s*(\d{1,3})\s+(.+)$/iu;
    const ANS_PFX_RE = /^(?:đáp án(?: đúng)?|dap an|correct answer|answer|chọn|kết quả)\s*(?:là|is)?\s*[:：=-]?\s*/iu;
    const NUM_ONLY_RE = /^(?:(?:câu|question|q|bài)\s*)?\d{1,3}\s*[:：.)–—-]?$/iu;
    const PAIR_RE = /(?:câu\s*)?(\d{1,3})\s*[:\-–.)=]?\s*([ABCD])(?![\p{L}\p{N}])/giu;

    // chuẩn hoá: bảng markdown, số câu nằm dòng riêng, "1-B, 2-C, 3-A" trên một dòng
    function normResult(text) {
        const raw = String(text || '').replace(/\r/g, '').split('\n').map(s => s.trim()).filter(Boolean);
        const out = [];
        for (let i = 0; i < raw.length; i++) {
            let l = raw[i];
            if (l.startsWith('|')) {
                const cells = l.split('|').map(cleanLine).filter(Boolean);
                if (!cells.length || cells.every(c => /^[-: ]+$/.test(c))) continue;
                l = cells.join(': ');
            } else {
                l = cleanLine(l);
            }
            if (!l) continue;
            if (NUM_ONLY_RE.test(l) && raw[i + 1]) {
                l = l.replace(/[:：.)–—-]+\s*$/, '') + ': ' + cleanLine(raw[++i]);
            }
            const pairs = [...l.matchAll(PAIR_RE)];
            if (pairs.length >= 2 && l.replace(PAIR_RE, '').replace(/[\s,;]+/g, '') === '') {
                pairs.forEach(p => out.push(`${p[1]}: ${p[2].toUpperCase()}`));
                continue;
            }
            out.push(l);
        }
        return out;
    }

    function parseResultLine(line) {
        const l = cleanLine(line);
        const m = l.match(RESULT_STRICT) || l.match(RESULT_LOOSE);
        if (!m) return null;
        let rest = m[2].trim();
        for (let i = 0; i < 2; i++) rest = rest.replace(ANS_PFX_RE, '').trim();
        return rest ? { num: Number(m[1]), rest } : null;
    }

    function answerLike(rest, isSA) {
        if (isSA) return rest.length > 0 && !/^(giải thích|explanation|lý do)/iu.test(rest);
        return /^[\s(\[]*[ABCD](?![\p{L}\p{N}])/u.test(rest) ||
            /^[\s(\[]*[abcd][.)\]](?:\s|$)/.test(rest) ||
            TF_ITEM_RE.test(rest) || TF_SEQ_RE.test(rest);
    }

    function countResults(text, expected, sa) {
        const saSet = new Set(sa || []);
        const seen = new Set();
        for (const line of normResult(text)) {
            const r = parseResultLine(line);
            if (r && expected.includes(r.num) && answerLike(r.rest, saSet.has(r.num))) seen.add(r.num);
        }
        return seen.size;
    }

    function parseMCRest(it, rest) {
        let m = rest.match(/^[\s(\[]*([ABCD](?:\s*(?:,|;|&|\/|\+|và|and)\s*[ABCD])*)(?![\p{L}\p{N}])/u);
        if (!m && it.multi) m = rest.match(/^[\s(\[]*([ABCD]{2,4})(?![\p{L}\p{N}])/u);
        if (!m) m = rest.match(/^[\s(\[]*([a-d])(?=\s*[.)\]:]|\s*$)/);
        let ans = m ? m[1].toUpperCase().replace(/[^ABCD]/g, '') : '';
        if (!ans) { // AI chỉ viết nội dung đáp án
            const target = norm(stripPrefix(rest));
            let idx = target.length > 1 ? it.options.findIndex(o => norm(o.text) === target) : -1;
            if (idx < 0 && target.length > 3) {
                idx = it.options.findIndex(o => {
                    const t = norm(o.text);
                    return t.length >= 4 && target.startsWith(t);
                });
            }
            if (idx >= 0) ans = L(idx);
        }
        ans = [...new Set(ans)].filter(c => c.charCodeAt(0) - 65 < it.options.length).join('');
        if (ans && !it.multi) ans = ans[0];
        return ans || null;
    }

    // câu điền ngắn: bỏ "Đáp án:", bỏ phần giải thích cùng dòng, tách nhiều chỗ trống bằng ;
    function parseSARest(it, rest) {
        let s = String(rest || '').split(/\s*(?:[-–—(]\s*)?(?:giải thích|explanation|lý do)\s*[:：)]/i)[0];
        s = cleanAnswer(s.replace(ANS_PFX_RE, ''));
        if (!s || s.length > 200) return null;
        if (it.blanks.length > 1) {
            s = s.split(/\s*[;|]\s*/).map(x => x.replace(/^\(?\d+[).:]\s*/, '')).join('; ');
        }
        return s;
    }

    const targetOf = (num, map) => map ? state.memory.get(map[num]) : state.items[num - 1];

    // AI chỉ liệt kê "B / C / A" mỗi dòng không kèm số câu -> gán theo thứ tự
    function seqFallback(lines, targets) {
        if (!targets.length || targets.some(it => it.type !== 'mc')) return [];
        const got = [];
        for (const l of lines) {
            const m = cleanLine(l).match(/^(?:đáp án\s*)?([ABCD])(?:[.):,]|\s|$)/u);
            if (m) got.push(m[1]);
        }
        return got.length === targets.length ? targets.map((it, i) => [it, got[i]]) : [];
    }

    async function applyAIResult(text, map) {
        const lines = normResult(text);
        const seen = new Set();
        let cur = null;

        const assign = async (it, ans, rest) => {
            const changed = JSON.stringify(it.answer) !== JSON.stringify(ans);
            it.answer = ans; it.solved = true; it.source = 'google-ai';
            if (changed || !it.aiText) it.aiText = rest;
            if (changed) applied.delete(it.card);
            if (CFG.aiAutoClick && !applied.has(it.card)) await pick(it);
        };

        for (const line of lines) {
            const r = parseResultLine(line);
            let matched = false;
            if (r) {
                const it = targetOf(r.num, map);
                if (it && !seen.has(it)) {
                    const ans = it.type === 'mc' ? parseMCRest(it, r.rest)
                        : it.type === 'sa' ? parseSARest(it, r.rest)
                            : parseTF(r.rest, it.statements.length);
                    if (ans) {
                        matched = true;
                        seen.add(it);
                        if (!it.solved || it.source === 'google-ai') {
                            await assign(it, ans, r.rest);
                            cur = it;
                        } else {
                            cur = null; // câu đã có đáp án trong HTML
                        }
                    }
                }
            }
            if (!matched && cur && cur.source === 'google-ai' && line.trim() && !cur.aiText.includes(line.trim())) {
                cur.aiText += '\n' + line.trim();
            }
        }

        if (!seen.size) {
            const targets = map
                ? Object.keys(map).map(Number).sort((a, b) => a - b).map(n => state.memory.get(map[n])).filter(Boolean)
                : state.items.filter(i => !i.solved);
            for (const [it, ch] of seqFallback(lines, targets)) {
                const ans = parseMCRest(it, ch);
                if (ans && (!it.solved || it.source === 'google-ai')) { await assign(it, ans, ch); seen.add(it); }
            }
        }
        // ghi chú đáp án AI ngay dưới câu hỏi trên trang
        for (const it of seen) {
            if (it.source === 'google-ai') { it.noteHtml = aiNote(it); cardNote(it); }
        }
        render();
        return seen.size;
    }

    // ---------- Phía tab quiz ----------
    function openTab(url) {
        try {
            if (typeof GM_openInTab === 'function') {
                return GM_openInTab(url, { active: CFG.aiTabActive, insert: true, setParent: true });
            }
        } catch (e) { /* ignore */ }
        window.open(url, '_blank');
        return null;
    }

    const pendingItems = () => state.items.filter(i => !i.solved);
    const aiBusy = () => !!(state.ai && state.ai.active);

    function copyPrompt() {
        if (!state.items.length) scan(true);
        const pending = pendingItems();
        if (!pending.length) { setStatus('Không còn câu nào chưa có đáp án.', 'warn'); return; }
        copy(buildPrompt(pending, ''));
        setStatus(`Đã copy prompt ${pending.length} câu. Dán vào Google AI, rồi dán kết quả vào ô "Dán kết quả AI".`, 'ok');
        uiToast(`📋 Đã copy prompt ${pending.length} câu`, 2200, 'ok');
    }

    function askGoogleAI(silent, onlyNew) {
        const pending = pendingItems().filter(i => !onlyNew || !i.asked);
        if (!pending.length) { if (!silent) setStatus('Không còn câu nào chưa có đáp án.', 'warn'); return; }
        if (aiBusy()) { setStatus('Đang chờ Google AI trả lời...', 'busy'); return; }

        const id = Date.now().toString(36);
        const token = `[#${id}]`;
        const prompt = buildPrompt(pending, token);
        const map = {};
        pending.forEach(it => { map[it.index + 1] = it.fp; it.asked = true; });
        copy(prompt); // luôn copy sẵn để dán thủ công nếu tự động không được

        if (!CFG.aiAutoPaste || !canCrossTab()) {
            openTab('https://www.google.com/search?udm=50');
            setStage(0);
            setTab('ai');
            setStatus(`Đã copy prompt ${pending.length} câu. Dán vào Google AI rồi dán kết quả vào ô bên dưới.`, 'info');
            render();
            return;
        }

        const q = encodeURIComponent(prompt);
        const viaUrl = q.length <= CFG.aiUrlMaxLen;
        const expected = pending.map(i => i.index + 1);
        store.set(JOB_KEY, {
            id, prompt, token, viaUrl, expected,
            sa: pending.filter(i => i.type === 'sa').map(i => i.index + 1),
            status: 'pending', ts: Date.now()
        });
        store.set(RESULT_KEY, null);

        const url = 'https://www.google.com/search?udm=50' + (viaUrl ? '&q=' + q : '') + '#tmquiz=' + id;
        const ai = { id, tab: openTab(url), active: true, t0: Date.now(), lastSeq: 0, expected, map };
        state.ai = ai;
        setStage(1);
        setStatus(`Đã gửi ${pending.length} câu cho Google AI, đang chờ trả lời...`, 'busy');
        render();
        pollResult(ai);
    }

    function cancelAI() {
        const ai = state.ai;
        if (!ai) return;
        ai.active = false;
        const job = store.get(JOB_KEY);
        if (job && job.id === ai.id) store.set(JOB_KEY, Object.assign({}, job, { status: 'cancelled' }));
        try { ai.tab && ai.tab.close && ai.tab.close(); } catch (e) { /* ignore */ }
        state.ai = null;
        setStage(0);
        setStatus('Đã dừng chờ Google AI.', 'warn');
        render();
    }

    function pollResult(ai) {
        if (state.ai !== ai || !ai.active) return;
        const job = store.get(JOB_KEY);
        if (job && job.id === ai.id && job.status === 'running' && state.aiStage < 2) setStage(2);
        const r = store.get(RESULT_KEY);
        if (r && r.id === ai.id && r.seq !== ai.lastSeq) {
            ai.lastSeq = r.seq;
            handleAIResult(ai, r);
        }
        if (state.ai !== ai || !ai.active) return;
        if (Date.now() - ai.t0 > CFG.aiTimeoutMs) {
            finishAI(ai, 'Hết thời gian chờ Google AI. Prompt đã copy, bạn có thể dán thủ công.', 'err');
            return;
        }
        setTimeout(() => pollResult(ai), 1000);
    }

    async function handleAIResult(ai, r) {
        if (r.error && !r.text) {
            finishAI(ai, r.error === 'no-input'
                ? 'Không thấy ô nhập của Google AI nên chưa tự dán được. Prompt đã copy, hãy dán thủ công.'
                : 'Tab Google AI báo lỗi: ' + r.error, 'err');
            return;
        }
        if (r.text) await applyAIResult(r.text, ai.map);
        const got = ai.expected.filter(n => {
            const it = state.memory.get(ai.map[n]);
            return it && it.source === 'google-ai';
        }).length;
        if (r.done) {
            const missing = ai.expected.filter(n => {
                const it = state.memory.get(ai.map[n]);
                return !(it && it.solved);
            });
            if (missing.length) {
                finishAI(ai, `Google AI trả lời ${got}/${ai.expected.length} câu. Thiếu câu: ${missing.join(', ')}. Bấm "Hỏi Google AI" lần nữa cho câu còn thiếu.`, 'warn');
            } else {
                finishAI(ai, `Google AI đã trả lời đủ ${got}/${ai.expected.length} câu.` +
                    (CFG.aiAutoClick ? '' : ' Bấm "Chọn tất cả" để áp dụng.'), 'ok');
            }
        } else {
            setStage(3);
            setStatus(`Google AI đang trả lời... (${got}/${ai.expected.length} câu)`, 'busy');
        }
    }

    function finishAI(ai, msg, kind) {
        if (!ai) return;
        ai.active = false;
        if (CFG.closeAITab) { try { ai.tab && ai.tab.close && ai.tab.close(); } catch (e) { /* ignore */ } }
        setStage(kind === 'err' ? -1 : 4);
        if (msg) setStatus(msg, kind || 'info');
        if (kind === 'ok') uiToast('🤖 ' + msg, 3500, 'ok');
        render();
    }

    // ---------- Phía tab Google AI: tự dán đề, tự đọc câu trả lời ----------
    const pageText = () => (document.body.innerText !== undefined ? document.body.innerText : document.body.textContent) || '';

    const visible = e => (e.getClientRects ? e.getClientRects().length > 0 : true) &&
        (!window.getComputedStyle || window.getComputedStyle(e).visibility !== 'hidden');

    function findInput() {
        const groups = [
            'textarea',
            '[contenteditable="true"],[contenteditable=""],[contenteditable="plaintext-only"]',
            '[role="textbox"]',
            'input[type="search"],input[type="text"]'
        ];
        for (const g of groups) {
            const el = [...document.querySelectorAll(g)].find(e => !e.disabled && !e.readOnly && visible(e));
            if (el) return el;
        }
        return null;
    }

    function setInputText(el, text) {
        el.focus();
        if (el.tagName === 'TEXTAREA' || el.tagName === 'INPUT') {
            const proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
            Object.getOwnPropertyDescriptor(proto, 'value').set.call(el, text);
            el.dispatchEvent(new Event('input', { bubbles: true }));
            el.dispatchEvent(new Event('change', { bubbles: true }));
        } else {
            let ok = false;
            try {
                document.execCommand('selectAll', false, null);
                ok = document.execCommand('insertText', false, text);
            } catch (e) { ok = false; }
            if (!ok) {
                el.textContent = text;
                el.dispatchEvent(new Event('input', { bubbles: true }));
            }
        }
    }

    function submitInput(el) {
        let n = el;
        for (let i = 0; i < 6 && n; i++, n = n.parentElement) {
            const btn = [...n.querySelectorAll('button,[role="button"]')].find(b =>
                !b.disabled && b.getAttribute('aria-disabled') !== 'true' &&
                /send|submit|gửi|search|tìm/i.test(`${b.getAttribute('aria-label') || ''} ${b.getAttribute('title') || ''} ${txt(b)}`));
            if (btn) { btn.click(); return 'button'; }
        }
        for (const type of ['keydown', 'keypress', 'keyup']) {
            el.dispatchEvent(new KeyboardEvent(type, { key: 'Enter', code: 'Enter', keyCode: 13, which: 13, bubbles: true, cancelable: true }));
        }
        return 'enter';
    }

    async function waitFor(fn, ms) {
        const t0 = Date.now();
        while (Date.now() - t0 < ms) {
            const v = fn();
            if (v) return v;
            await sleep(300);
        }
        return null;
    }

    // thông báo nhỏ trên tab Google AI (tab này không có giao diện chính)
    function agentToast(msg, ms) {
        if (!document.body) return;
        let t = document.querySelector('#tm-ai-toast');
        if (!t) {
            t = document.createElement('div');
            t.id = 'tm-ai-toast';
            t.style.cssText = 'position:fixed;left:50%;bottom:24px;transform:translateX(-50%);z-index:2147483647;' +
                'padding:10px 16px;border-radius:14px;background:rgba(15,17,26,.96);color:#fff;font:13px system-ui,sans-serif;' +
                'border:1px solid rgba(124,131,255,.45);box-shadow:0 12px 34px rgba(0,0,0,.45)';
            document.body.appendChild(t);
        }
        t.textContent = msg;
        clearTimeout(t._tm);
        if (ms) t._tm = setTimeout(() => t.remove(), ms);
    }

    function runAgent() {
        const m = location.hash.match(/tmquiz=([\w-]+)/);
        if (!m || !isTop || !canCrossTab()) return false;
        const job = store.get(JOB_KEY);
        if (!job || job.id !== m[1] || job.status !== 'pending') return false;
        job.status = 'running';
        store.set(JOB_KEY, job);
        agentMain(job);
        return true;
    }

    async function agentMain(job) {
        let seq = 0;
        const send = o => store.set(RESULT_KEY, Object.assign({ id: job.id, seq: ++seq, ts: Date.now() }, o));
        const promptLines = new Set(job.prompt.split('\n').map(norm).filter(Boolean));
        const cancelled = () => {
            const j = store.get(JOB_KEY);
            return !j || j.id !== job.id || j.status === 'cancelled';
        };

        const pasteAndSend = async () => {
            const input = await waitFor(() => cancelled() || findInput(), 25000);
            if (cancelled()) return false;
            if (!input) {
                send({ error: 'no-input', done: true });
                agentToast('Không thấy ô nhập, hãy dán thủ công (prompt đã copy).');
                return false;
            }
            setInputText(input, job.prompt);
            await sleep(600);
            submitInput(input);
            return true;
        };

        try {
            agentToast('🤖 AI Quiz Solver: đang gửi đề cho Google AI...');
            if (job.viaUrl) {
                // prompt đi qua URL; nếu sau 20s trang chưa hiện đề thì dán tay vào ô nhập
                const ok = await waitFor(() => cancelled() || pageText().includes(job.token), 20000);
                if (!ok && !(await pasteAndSend())) return;
            } else if (!(await pasteAndSend())) {
                return;
            }
            if (cancelled()) { agentToast('Đã dừng theo yêu cầu từ trang quiz.', 2500); return; }
            agentToast('🤖 AI Quiz Solver: đang chờ câu trả lời...');

            const t0 = Date.now();
            let lastText = '', lastSent = '', stable = 0;
            while (Date.now() - t0 < CFG.aiTimeoutMs - 8000) {
                await sleep(1000);
                if (cancelled()) { agentToast('Đã dừng theo yêu cầu từ trang quiz.', 2500); return; }
                const full = pageText();
                const i = full.lastIndexOf(job.token);
                let slice = '';
                if (i >= 0) slice = full.slice(i + job.token.length);
                else if (Date.now() - t0 > 45000) { // không thấy mã đề: loại các dòng của đề rồi đọc phần còn lại
                    slice = full.split('\n').filter(l => !promptLines.has(norm(l))).join('\n');
                }
                const found = slice ? countResults(slice, job.expected, job.sa) : 0;

                if (found > 0 && slice !== lastSent) { send({ text: slice, done: false }); lastSent = slice; }
                stable = slice === lastText ? stable + 1 : 0;
                lastText = slice;

                if (found >= job.expected.length && stable >= 4) {
                    send({ text: slice, done: true });
                    agentToast('✓ Xong, kết quả đã gửi về trang quiz.', 4000);
                    return;
                }
                // AI đã dừng viết nhưng thiếu câu / viết nội dung đáp án thay vì chữ cái
                if (stable >= 15 && slice.length > 30) {
                    send({ text: slice, done: true });
                    agentToast('✓ Đã gửi kết quả (có thể thiếu câu).', 4000);
                    return;
                }
            }
            send({ text: lastSent || '', done: true, error: lastSent ? null : 'timeout' });
        } catch (e) {
            send({ error: String((e && e.message) || e), done: true });
        }
    }

    // =========================================================
    // LUỒNG "BẮT ĐẦU"
    // =========================================================
    async function waitForQuiz(ms = 15000) {
        const t0 = Date.now();
        while (Date.now() - t0 < ms) {
            if (detectItems(true).items.length) { await sleep(600); return true; }
            await sleep(300);
        }
        return false;
    }

    async function onStart(force) {
        if (state.starting || (state.started && !force)) return false;
        state.starting = true;
        try {
            setStatus('Đang tìm quiz trên trang...', 'busy');
            if (!(await waitForQuiz())) return false;
            state.started = true;
            ensureUI();
            createPanel(CFG.openOnStart);
            scan(true);
            await solveAllByKey();

            const total = state.items.length;
            const left = state.items.filter(i => !i.solved).length;
            setStatus((left
                ? `Đã tick ${total - left}/${total} câu từ đáp án trong HTML. Còn ${left} câu cần AI.`
                : `Xong! Đã tick ${total}/${total} câu.`) + ` (${state.mode})`, left ? 'info' : 'ok');

            if (left && CFG.autoAskAI) askGoogleAI(true, false);
            return true;
        } finally {
            state.starting = false;
        }
    }

    function hookStartButton() {
        document.addEventListener('click', e => {
            if (isOurs(e.target)) return;
            const b = e.target.closest && e.target.closest('button, a, input[type="button"], input[type="submit"], [role="button"]');
            if (!b) return;
            const hit = CFG.startBtn
                ? b.matches(CFG.startBtn)
                : CFG.startRegex.test(txt(b) || b.value || '');
            if (hit) onStart();
        }, true);
    }

    // =========================================================
    // THEO DÕI TRANG ĐỘNG (DOM đổi, URL đổi, tab hiện lại)
    // =========================================================
    function relevant(m) {
        if (isOurs(m.target)) return false;
        if (m.type === 'attributes') {
            if (m.target.classList && m.target.classList.contains('tm-ai-note')) return false;
            if (m.attributeName === 'class') {
                return String(m.oldValue || '').replace(OUR_CLS, '').replace(/\s+/g, ' ').trim() !==
                    String(m.target.getAttribute('class') || '').replace(OUR_CLS, '').replace(/\s+/g, ' ').trim();
            }
            return true;
        }
        const nodes = [...m.addedNodes, ...m.removedNodes];
        if (!nodes.length) return false;
        return nodes.some(n => {
            if (n.nodeType === 3) return !!n.nodeValue.trim();
            if (n.nodeType !== 1) return false;
            return !(isOurs(n) || n.classList.contains('tm-ai-note'));
        });
    }

    let scanTimer = null, lastScan = 0;
    function schedule(delay) {
        clearTimeout(scanTimer);
        const wait = Math.max(delay === undefined ? CFG.scanDebounce : delay,
            CFG.scanThrottle - (Date.now() - lastScan));
        scanTimer = setTimeout(runScan, Math.max(0, wait));
    }

    const panelOpen = () => !!(state.panel && !state.panel.hidden);

    async function runScan() {
        if (state.running || state.scanning || state.starting) { schedule(); return; }
        lastScan = Date.now();
        ensureUI();
        scan(state.started || panelOpen());
        if (state.started) {
            await solveAllByKey();
            if (CFG.autoAskNew && !aiBusy() && state.items.some(i => !i.solved && !i.asked)) {
                askGoogleAI(true, true);
            }
        }
    }

    function watch() {
        new MutationObserver(muts => {
            if (muts.some(relevant)) schedule();
        }).observe(document.documentElement, {
            childList: true, subtree: true,
            attributes: true, attributeFilter: ['class', 'hidden'], attributeOldValue: true
        });
        document.addEventListener('visibilitychange', () => { if (!document.hidden) schedule(200); });
        window.addEventListener('popstate', () => schedule(400));
        window.addEventListener('hashchange', () => schedule(400));

        // dự phòng: đổi URL kiểu SPA, thân trang bị thay, trang tải quiz rất muộn
        let lastHref = location.href, ticks = 0;
        setInterval(() => {
            if (document.hidden) return;
            ticks++;
            ensureUI();
            if (location.href !== lastHref) { lastHref = location.href; schedule(300); return; }
            if (!state.items.length && ticks % 3 === 0 && ticks < 300) schedule(0);
        }, 1000);
    }

    // Chọn / điền đáp án đúng cho tất cả câu đã có đáp án (Shift + bấm = làm lại toàn bộ)
    async function selectAll(force) {
        if (state.running) return;
        if (!state.items.length) scan(true);
        const solved = state.items.filter(i => i.solved && i.answer != null);
        if (!solved.length) {
            const m = 'Chưa có đáp án nào để chọn. Bấm "Bắt đầu" hoặc "Hỏi Google AI" trước.';
            setStatus(m, 'warn'); uiToast(m, 3000, 'warn');
            return;
        }
        if (force) solved.forEach(i => applied.delete(i.card));
        const todo = solved.filter(i => !applied.has(i.card));
        state.running = true;
        try {
            for (const it of todo) await pick(it);
        } finally {
            state.running = false;
        }
        render();
        const left = state.items.length - solved.length;
        const m = todo.length
            ? `Đã chọn ${todo.length} câu` + (left ? `, còn ${left} câu chưa có đáp án.` : '. Đã đủ đáp án cho tất cả các câu.')
            : `${solved.length} câu có đáp án đều đã được chọn rồi` + (left ? ` (còn ${left} câu chưa có đáp án).` : '.');
        setStatus(m, 'ok');
        uiToast('✓ ' + m, 3500, 'ok');
    }

    // =========================================================
    // GIAO DIỆN (Shadow DOM: CSS của trang không ảnh hưởng, panel cũng không làm bẩn trang)
    // =========================================================
    const FAB_C = 194.78;   // chu vi vòng tiến độ ở nút tròn (r=31)
    const RING_C = 169.65;  // chu vi vòng tiến độ trong panel (r=27)

    const UI_CSS = `
    :host{all:initial}
    *{box-sizing:border-box;margin:0}
    [hidden]{display:none!important}
    .root{
        --bg:rgba(15,17,27,.97);--sf:rgba(255,255,255,.05);--sf2:rgba(255,255,255,.09);--bd:rgba(255,255,255,.1);
        --tx:#eceefb;--mu:rgba(236,238,251,.58);--ac:#7c83ff;--ac2:#a78bfa;--ok:#34d399;--wa:#fbbf24;--er:#f87171;
        --ring:rgba(255,255,255,.1);--sh:0 24px 64px rgba(0,0,0,.55),0 2px 8px rgba(0,0,0,.35);--inp:rgba(0,0,0,.28);
        font:13px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;color:var(--tx);-webkit-font-smoothing:antialiased}
    .root[data-theme="light"]{
        --bg:rgba(255,255,255,.98);--sf:rgba(15,23,42,.04);--sf2:rgba(15,23,42,.08);--bd:rgba(15,23,42,.12);
        --tx:#0f172a;--mu:rgba(15,23,42,.58);--ac:#4f46e5;--ac2:#7c3aed;--ok:#059669;--wa:#d97706;--er:#dc2626;
        --ring:rgba(15,23,42,.1);--sh:0 24px 60px rgba(15,23,42,.22),0 2px 8px rgba(15,23,42,.12);--inp:rgba(15,23,42,.05)}
    button{font-family:inherit;color:inherit;cursor:pointer;border:0;background:none;padding:0}
    button:focus-visible,input:focus-visible,textarea:focus-visible,select:focus-visible,summary:focus-visible{outline:2px solid var(--ac);outline-offset:1px}

    /* ---- nút tròn ---- */
    .fab{position:fixed;right:18px;bottom:18px;width:56px;height:56px;border-radius:50%;display:flex;align-items:center;justify-content:center;
        font-size:23px;color:#fff;cursor:pointer;user-select:none;touch-action:none;z-index:1;
        background:linear-gradient(135deg,#6366f1,#8b5cf6);box-shadow:0 10px 30px rgba(79,70,229,.45),0 2px 6px rgba(0,0,0,.3);transition:transform .15s}
    .fab:hover{transform:scale(1.07)}
    .fab svg{position:absolute;left:-6px;top:-6px;width:68px;height:68px;transform:rotate(-90deg);pointer-events:none}
    .fab .trk{fill:none;stroke:rgba(99,102,241,.28);stroke-width:3.5}
    .fab .prg{fill:none;stroke:#34d399;stroke-width:3.5;stroke-linecap:round;stroke-dasharray:${FAB_C};stroke-dashoffset:${FAB_C};transition:stroke-dashoffset .4s ease}
    .fab.busy::after{content:"";position:absolute;left:-6px;top:-6px;right:-6px;bottom:-6px;border-radius:50%;border:2px solid rgba(167,139,250,.8);animation:pulse 1.4s ease-out infinite}
    .fab .bdg{position:absolute;top:-8px;right:-8px;min-width:22px;height:22px;padding:0 6px;border-radius:11px;background:#f59e0b;color:#fff;
        font:700 11px/22px system-ui,sans-serif;text-align:center;font-style:normal;box-shadow:0 2px 8px rgba(0,0,0,.35)}
    .fab .bdg[data-k="ok"]{background:#10b981}
    @keyframes pulse{from{transform:scale(.92);opacity:.9}to{transform:scale(1.28);opacity:0}}

    /* ---- panel ---- */
    .panel{position:fixed;top:16px;right:16px;width:408px;max-width:calc(100vw - 16px);max-height:calc(100vh - 32px);display:flex;flex-direction:column;
        background:var(--bg);color:var(--tx);border:1px solid var(--bd);border-radius:22px;box-shadow:var(--sh);overflow:hidden;z-index:2;
        -webkit-backdrop-filter:blur(18px) saturate(1.3);backdrop-filter:blur(18px) saturate(1.3);animation:pin .2s cubic-bezier(.2,.8,.2,1)}
    @keyframes pin{from{opacity:0;transform:translateY(10px) scale(.98)}to{opacity:1;transform:none}}
    .panel.min{max-height:none}
    .panel.min .bd{display:none}
    .hd{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:12px 12px 12px 14px;cursor:grab;touch-action:none;user-select:none;flex:none;
        background:linear-gradient(135deg,rgba(124,131,255,.22),rgba(167,139,250,.08));border-bottom:1px solid var(--bd)}
    .hd.drag{cursor:grabbing}
    .brand{display:flex;align-items:center;gap:11px;min-width:0}
    .logo{width:36px;height:36px;border-radius:12px;display:flex;align-items:center;justify-content:center;font-size:19px;flex:none;
        background:linear-gradient(135deg,#6366f1,#8b5cf6);box-shadow:0 4px 14px rgba(99,102,241,.45)}
    .ttl b{display:block;font-size:14.5px;line-height:1.2;letter-spacing:.1px}
    .ttl small{display:block;font-size:10.5px;color:var(--mu);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:230px}
    .hbtns{display:flex;gap:4px;flex:none}
    .ib{width:30px;height:30px;border-radius:10px;font-size:14px;line-height:1;color:var(--mu);transition:background .12s,color .12s}
    .ib:hover{background:var(--sf2);color:var(--tx)}
    .bd{display:flex;flex-direction:column;gap:10px;padding:12px;overflow-y:auto;overscroll-behavior:contain;flex:1 1 auto;min-height:0}
    .bd::-webkit-scrollbar,.list::-webkit-scrollbar{width:6px}
    .bd::-webkit-scrollbar-thumb,.list::-webkit-scrollbar-thumb{background:var(--sf2);border-radius:3px}

    /* tổng quan */
    .sum{display:flex;align-items:center;gap:14px;padding:12px;border-radius:16px;background:var(--sf);border:1px solid var(--bd)}
    .ring{position:relative;width:68px;height:68px;flex:none}
    .ring svg{width:68px;height:68px;transform:rotate(-90deg)}
    .ring .trk{fill:none;stroke:var(--ring);stroke-width:6}
    .ring .prg{fill:none;stroke:var(--ok);stroke-width:6;stroke-linecap:round;stroke-dasharray:${RING_C};stroke-dashoffset:${RING_C};transition:stroke-dashoffset .45s ease}
    .rt{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;line-height:1.1}
    .rt b{font-size:15px}.rt small{font-size:9.5px;color:var(--mu);margin-top:2px}
    .stats{flex:1;display:grid;grid-template-columns:repeat(3,1fr);gap:6px}
    .st{text-align:center;padding:8px 2px;border-radius:12px;background:var(--sf)}
    .st b{display:block;font-size:17px;line-height:1.1}
    .st span{display:block;font-size:9.5px;color:var(--mu);margin-top:3px;text-transform:uppercase;letter-spacing:.04em}
    .st i{display:inline-block;width:6px;height:6px;border-radius:50%;margin-right:4px;vertical-align:middle;position:relative;top:-1px}
    .st .k{background:var(--ok)}.st .a{background:var(--ac2)}.st .n{background:var(--wa)}

    /* trạng thái */
    .stat{display:flex;align-items:flex-start;gap:9px;padding:9px 11px;border-radius:13px;font-size:12.5px;word-break:break-word;
        background:rgba(124,131,255,.12);border:1px solid rgba(124,131,255,.22)}
    .stat[data-k="ok"]{background:rgba(52,211,153,.12);border-color:rgba(52,211,153,.28)}
    .stat[data-k="warn"]{background:rgba(251,191,36,.12);border-color:rgba(251,191,36,.3)}
    .stat[data-k="err"]{background:rgba(248,113,113,.12);border-color:rgba(248,113,113,.3)}
    .si{flex:none;width:18px;text-align:center;line-height:1.35}
    .sp{display:inline-block;width:12px;height:12px;border-radius:50%;border:2px solid var(--sf2);border-top-color:var(--ac);animation:spin .8s linear infinite;vertical-align:middle}
    @keyframes spin{to{transform:rotate(360deg)}}

    /* các bước AI */
    .steps{display:flex;align-items:center;gap:6px;padding:2px 4px}
    .stp{display:flex;align-items:center;gap:6px;font-size:11px;color:var(--mu);white-space:nowrap}
    .stp i{width:20px;height:20px;border-radius:50%;display:flex;align-items:center;justify-content:center;font-style:normal;font-size:10.5px;font-weight:700;background:var(--sf2)}
    .stp.on{color:var(--tx)}.stp.on i{background:var(--ac);color:#fff;animation:pulse2 1.2s ease-in-out infinite}
    .stp.done{color:var(--tx)}.stp.done i{background:var(--ok);color:#fff}
    .stp.err{color:var(--er)}.stp.err i{background:var(--er);color:#fff}
    .stp .bar{display:none}
    .sbar{flex:1;height:2px;border-radius:1px;background:var(--sf2);min-width:8px}
    .stp.done+.sbar{background:var(--ok)}
    @keyframes pulse2{50%{box-shadow:0 0 0 5px rgba(124,131,255,.25)}}

    /* nút */
    .acts{display:grid;grid-template-columns:1fr 1fr;gap:7px}
    .btn{min-height:38px;padding:0 12px;border-radius:12px;background:var(--sf2);font-size:12.5px;font-weight:600;display:flex;align-items:center;justify-content:center;gap:6px;
        transition:filter .12s,transform .08s,background .12s}
    .btn:hover{filter:brightness(1.15)}.btn:active{transform:scale(.97)}
    .btn:disabled{opacity:.4;cursor:not-allowed;transform:none;filter:none}
    .btn.pri{background:linear-gradient(135deg,#6366f1,#8b5cf6);color:#fff}
    .btn.ai{background:linear-gradient(135deg,#8b5cf6,#d946ef);color:#fff}
    .btn.ai.stop{background:linear-gradient(135deg,#ef4444,#f97316)}
    .btn.ok{background:linear-gradient(135deg,#10b981,#059669);color:#fff;grid-column:1/-1;min-height:42px;font-size:13px}
    .btn.sm{min-height:32px;font-size:12px}

    /* tab */
    .tabs{display:flex;gap:3px;padding:3px;border-radius:13px;background:var(--sf);border:1px solid var(--bd)}
    .tabs button{flex:1;min-height:30px;border-radius:10px;font-size:12px;font-weight:600;color:var(--mu);display:flex;align-items:center;justify-content:center;gap:6px;transition:background .12s,color .12s}
    .tabs button.on{background:var(--sf2);color:var(--tx);box-shadow:0 1px 3px rgba(0,0,0,.18)}
    .tabs em{font-style:normal;font-size:10px;padding:1px 6px;border-radius:8px;background:var(--sf2);color:var(--mu)}
    .tabs button.on em{background:var(--ac);color:#fff}
    .pane{display:flex;flex-direction:column;gap:9px}

    /* danh sách câu */
    .seg{display:flex;gap:4px;flex-wrap:wrap}
    .seg button{padding:5px 10px;border-radius:999px;font-size:11.5px;font-weight:600;color:var(--mu);background:var(--sf);border:1px solid transparent;transition:all .12s}
    .seg button em{font-style:normal;opacity:.7;margin-left:4px}
    .seg button.on{color:var(--tx);background:rgba(124,131,255,.2);border-color:rgba(124,131,255,.45)}
    .list{max-height:min(46vh,420px);min-height:90px;overflow-y:auto;overscroll-behavior:contain;display:flex;flex-direction:column;gap:7px;padding-right:2px}
    .q{display:flex;gap:10px;align-items:flex-start;padding:10px;border-radius:14px;background:var(--sf);border:1px solid var(--bd);cursor:pointer;transition:background .12s,border-color .12s}
    .q:hover{background:var(--sf2)}
    .qn{width:26px;height:26px;border-radius:9px;flex:none;display:flex;align-items:center;justify-content:center;font-size:11.5px;font-weight:700;background:var(--sf2);color:var(--mu)}
    .q.ok .qn{background:rgba(52,211,153,.2);color:var(--ok)}
    .q.ai .qn{background:rgba(167,139,250,.22);color:var(--ac2)}
    .q.no .qn{background:rgba(251,191,36,.18);color:var(--wa)}
    .qb{flex:1;min-width:0}
    .qt{font-size:12px;color:var(--tx);opacity:.85;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;word-break:break-word}
    .qm{display:flex;align-items:center;gap:5px;flex-wrap:wrap;margin-top:6px}
    .chip{font-size:9.5px;padding:2px 7px;border-radius:7px;background:var(--sf2);color:var(--mu);font-weight:600}
    .chip.w{background:rgba(251,191,36,.18);color:var(--wa)}
    .src{font-size:9.5px;font-weight:700;letter-spacing:.04em;padding:2px 6px;border-radius:7px;color:#fff;background:var(--ok)}
    .q.ai .src{background:var(--ac2)}
    .pill{min-width:24px;height:24px;padding:0 8px;border-radius:8px;display:inline-flex;align-items:center;justify-content:center;font-weight:700;font-size:12px;
        background:rgba(124,131,255,.2);color:var(--tx);border:1px solid rgba(124,131,255,.4)}
    .pill.t{background:rgba(52,211,153,.18);border-color:rgba(52,211,153,.45)}
    .pill.f{background:rgba(248,113,113,.16);border-color:rgba(248,113,113,.45)}
    .pill.txt{max-width:100%;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;justify-content:flex-start}
    .mu{color:var(--mu);font-size:11.5px}
    .wt{display:inline-flex;align-items:center;gap:6px;color:var(--ac2);font-size:11.5px;font-weight:600}
    .qa{display:flex;flex-direction:column;gap:5px;flex:none}
    .mini{min-width:52px;height:26px;padding:0 10px;border-radius:9px;font-size:11px;font-weight:700;background:var(--sf2);transition:background .12s}
    .mini:hover{background:rgba(124,131,255,.35)}
    .mini.ghost{background:transparent;color:var(--mu);border:1px solid var(--bd)}
    .qx{margin-top:8px;padding:8px 10px;border-radius:10px;background:var(--inp)}
    .qx pre{white-space:pre-wrap;word-break:break-word;font:11.5px/1.55 inherit;font-family:inherit;color:var(--tx);opacity:.85;max-height:170px;overflow-y:auto}
    .empty{padding:22px 10px;text-align:center;color:var(--mu);border:1px dashed var(--bd);border-radius:14px}

    /* ô cài đặt */
    .card{padding:10px 12px;border-radius:14px;background:var(--sf);border:1px solid var(--bd)}
    .card h4{font-size:11px;text-transform:uppercase;letter-spacing:.06em;color:var(--mu);margin-bottom:4px;font-weight:700}
    .note{font-size:11.5px;color:var(--mu);line-height:1.5}
    .sw{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:8px 0;cursor:pointer;position:relative}
    .sw+.sw{border-top:1px solid var(--bd)}
    .sw input{position:absolute;opacity:0;pointer-events:none}
    .swt b{display:block;font-weight:600;font-size:12.5px}
    .swt small{display:block;color:var(--mu);font-size:11px;margin-top:1px}
    .knob{width:38px;height:22px;border-radius:11px;background:var(--sf2);position:relative;flex:none;transition:background .15s}
    .knob::after{content:"";position:absolute;top:3px;left:3px;width:16px;height:16px;border-radius:50%;background:#fff;box-shadow:0 1px 3px rgba(0,0,0,.35);transition:transform .15s}
    .sw input:checked~.knob{background:linear-gradient(135deg,var(--ac),var(--ac2))}
    .sw input:checked~.knob::after{transform:translateX(16px)}
    .sw input:focus-visible~.knob{outline:2px solid var(--ac);outline-offset:2px}
    .two{display:grid;grid-template-columns:1fr 1fr;gap:7px}
    .tx{display:block;width:100%;margin-top:7px;padding:8px 10px;border-radius:10px;border:1px solid var(--bd);background:var(--inp);color:var(--tx);font:12px ui-monospace,SFMono-Regular,Consolas,monospace}
    textarea.tx{min-height:96px;resize:vertical;font-size:12px}
    details.card summary{cursor:pointer;font-weight:600;font-size:12.5px;list-style:none;display:flex;align-items:center;justify-content:space-between}
    details.card summary::-webkit-details-marker{display:none}
    details.card summary::after{content:"▾";color:var(--mu);transition:transform .15s}
    details.card[open] summary::after{transform:rotate(180deg)}
    details.card[open] summary{margin-bottom:6px}
    .foot{text-align:center;font-size:10.5px;color:var(--mu);padding:2px 0 4px}
    kbd{font:inherit;font-size:10px;padding:1px 5px;border-radius:5px;background:var(--sf2);border:1px solid var(--bd)}

    /* thông báo nổi */
    .toast{position:fixed;left:50%;bottom:24px;transform:translate(-50%,16px);opacity:0;pointer-events:none;z-index:3;max-width:min(520px,calc(100vw - 24px));
        padding:10px 16px;border-radius:14px;background:var(--bg);color:var(--tx);border:1px solid var(--bd);box-shadow:var(--sh);font-size:13px;transition:opacity .2s,transform .2s}
    .toast.on{opacity:1;transform:translate(-50%,0)}
    .toast[data-k="ok"]{border-color:rgba(52,211,153,.5)}
    .toast[data-k="warn"]{border-color:rgba(251,191,36,.55)}

    @media (max-width:480px){
        .panel{left:8px!important;right:8px!important;top:auto!important;bottom:8px!important;width:auto!important;max-height:84vh}
        .stats{gap:4px}
    }
    @media (prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}
    `;

    const PAGE_CSS = `
    .tm-ai-note{margin-top:10px;padding:10px 12px;border-radius:12px;border:1px solid rgba(99,102,241,.35);border-left:4px solid #6366f1;
        background:rgba(99,102,241,.1);color:inherit;font:13px/1.5 system-ui,-apple-system,"Segoe UI",sans-serif}
    .tm-ai-note div{margin-top:4px;opacity:.8;font-size:12px}
    .tm-ai-picked{outline:2px solid rgba(16,185,129,.75)!important;outline-offset:2px;background-color:rgba(16,185,129,.12)!important}
    .tm-ai-flash{outline:3px solid rgba(124,131,255,.95)!important;outline-offset:4px;border-radius:6px}`;

    function injectPageCSS() {
        if (document.getElementById('tm-ai-style') || !document.head) return;
        const s = document.createElement('style');
        s.id = 'tm-ai-style';
        s.textContent = PAGE_CSS;
        document.head.appendChild(s);
    }

    // ---------- gốc Shadow DOM ----------
    function resolvedTheme() {
        if (CFG.theme === 'light' || CFG.theme === 'dark') return CFG.theme;
        return (window.matchMedia && matchMedia('(prefers-color-scheme: light)').matches) ? 'light' : 'dark';
    }
    function applyTheme() {
        if (state.rootEl) state.rootEl.dataset.theme = resolvedTheme();
    }

    function mountRoot() {
        const parent = document.documentElement;
        if (!parent) return false;
        if (!state.host) {
            const host = document.createElement('div');
            host.id = 'tm-ai-root';
            host.style.cssText = 'all:initial;display:block;position:fixed;top:0;left:0;width:0;height:0;z-index:2147483647;';
            const sh = host.attachShadow({ mode: 'open' });
            sh.innerHTML = `<style>${UI_CSS}</style><div class="root" id="root"></div>`;
            // bàn phím trong ô nhập không rò ra phím tắt của trang (trừ Ctrl+Shift+...)
            ['keydown', 'keyup', 'keypress'].forEach(t => sh.addEventListener(t, e => {
                const el = e.composedPath()[0];
                if (el && /^(INPUT|TEXTAREA|SELECT)$/.test(el.tagName) && !(e.ctrlKey && e.shiftKey)) e.stopPropagation();
            }));
            state.host = host;
            state.shadow = sh;
            state.rootEl = sh.querySelector('#root');
            applyTheme();
        }
        if (!state.host.isConnected) parent.appendChild(state.host);
        return true;
    }

    function ensureUI() {
        if (!document.documentElement) return;
        injectPageCSS();
        const need = (isTop && CFG.alwaysLauncher) || state.items.length || state.panel;
        if (!need) return;
        if (!mountRoot()) return;
        createLauncher();
    }

    // ---------- thông báo ----------
    function uiToast(msg, ms, kind) {
        if (!mountRoot()) return;
        let t = state.rootEl.querySelector('.toast');
        if (!t) {
            t = document.createElement('div');
            t.className = 'toast';
            state.rootEl.appendChild(t);
        }
        t.dataset.k = kind || 'info';
        t.textContent = msg;
        t.classList.add('on');
        clearTimeout(t._tm);
        t._tm = setTimeout(() => t.classList.remove('on'), ms || 3200);
    }

    const $ui = sel => (state.panel ? state.panel.querySelector(sel) : null);

    function setStatus(msg, kind) {
        state.status = { msg, kind: kind || 'info' };
        paintStatus();
    }
    function paintStatus() {
        const box = $ui('#status');
        if (!box) return;
        const k = state.status.kind;
        box.dataset.k = k;
        $ui('#s-ico').innerHTML = k === 'busy' ? '<i class="sp"></i>' : k === 'ok' ? '✓' : k === 'warn' ? '⚠' : k === 'err' ? '✕' : 'ℹ';
        $ui('#s-msg').textContent = state.status.msg;
    }

    let stageTimer = null;
    function setStage(n) {
        if (n === -1) state.stageFrom = state.aiStage > 0 ? state.aiStage : Math.max(1, state.stageFrom);
        state.aiStage = n;
        clearTimeout(stageTimer);
        if (n === 4) stageTimer = setTimeout(() => { if (state.aiStage === 4) { state.aiStage = 0; paintStage(); } }, 9000);
        paintStage();
    }
    function paintStage() {
        const box = $ui('#steps');
        if (!box) return;
        const st = state.aiStage;
        box.hidden = st === 0;
        box.querySelectorAll('.stp').forEach(x => {
            const s = Number(x.dataset.s);
            let c = '';
            if (st === 4) c = 'done';
            else if (st === -1) { const f = Math.max(1, state.stageFrom); c = s < f ? 'done' : s === f ? 'err' : ''; }
            else if (st > 0) c = s < st ? 'done' : s === st ? 'on' : '';
            x.className = 'stp ' + c;
        });
    }

    function setTab(t) {
        state.tab = t;
        const p = state.panel;
        if (!p) return;
        p.querySelectorAll('.tabs [data-tab]').forEach(b => b.classList.toggle('on', b.dataset.tab === t));
        p.querySelectorAll('.pane').forEach(pn => { pn.hidden = pn.dataset.pane !== t; });
    }

    // ---------- nút tròn ----------
    function createLauncher() {
        if (state.launcher || !mountRoot()) return;
        const b = document.createElement('div');
        b.className = 'fab';
        b.title = 'AI Quiz Solver (Ctrl+Shift+Q)';
        b.setAttribute('role', 'button');
        b.setAttribute('aria-label', 'Mở AI Quiz Solver');
        b.innerHTML = '<svg viewBox="0 0 68 68" aria-hidden="true"><circle class="trk" cx="34" cy="34" r="31"/><circle class="prg" cx="34" cy="34" r="31"/></svg>' +
            '<span class="ico">🤖</span><i class="bdg" style="display:none"></i>';
        state.rootEl.appendChild(b);
        state.launcher = b;

        const pos = store.get(POS_KEY);
        if (pos && typeof pos.left === 'number' && typeof pos.top === 'number') {
            b.style.left = Math.min(Math.max(0, pos.left), innerWidth - 56) + 'px';
            b.style.top = Math.min(Math.max(0, pos.top), innerHeight - 56) + 'px';
            b.style.right = 'auto'; b.style.bottom = 'auto';
        }

        let sx, sy, ox, oy, dragging = false, down = false;
        b.addEventListener('pointerdown', e => {
            down = true; dragging = false;
            sx = e.clientX; sy = e.clientY;
            const r = b.getBoundingClientRect();
            ox = r.left; oy = r.top;
            b.setPointerCapture(e.pointerId);
        });
        b.addEventListener('pointermove', e => {
            if (!down) return;
            const dx = e.clientX - sx, dy = e.clientY - sy;
            if (!dragging && Math.hypot(dx, dy) < 6) return;
            dragging = true;
            b.style.left = Math.min(Math.max(0, ox + dx), innerWidth - 56) + 'px';
            b.style.top = Math.min(Math.max(0, oy + dy), innerHeight - 56) + 'px';
            b.style.right = 'auto'; b.style.bottom = 'auto';
        });
        b.addEventListener('pointerup', e => {
            down = false;
            try { b.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
            if (dragging) {
                const r = b.getBoundingClientRect();
                store.set(POS_KEY, { left: r.left, top: r.top });
            } else {
                togglePanel();
            }
        });
        updateLauncher();
    }

    function updateLauncher() {
        const b = state.launcher;
        if (!b) return;
        const total = state.items.length;
        const done = state.items.filter(i => i.solved).length;
        b.querySelector('.ico').textContent = panelOpen() ? '✕' : '🤖';
        const bd = b.querySelector('.bdg');
        bd.textContent = total || '';
        bd.style.display = total ? 'block' : 'none';
        bd.dataset.k = total && done === total ? 'ok' : 'part';
        bd.title = `${done}/${total} câu đã có đáp án`;
        b.querySelector('.prg').style.strokeDashoffset = String(FAB_C * (1 - (total ? done / total : 0)));
        b.classList.toggle('busy', aiBusy() || state.running || state.starting);
    }

    function togglePanel(force) {
        createLauncher();
        if (!state.panel) {
            if (force === false) return;
            createPanel(true);
            scan(true);
            return;
        }
        const show = force === undefined ? state.panel.hidden : force;
        state.panel.hidden = !show;
        if (show) schedule(100);
        updateLauncher();
    }

    // ---------- panel ----------
    const swHtml = (k, label, hint) =>
        `<label class="sw"><span class="swt"><b>${label}</b>${hint ? `<small>${hint}</small>` : ''}</span>` +
        `<input type="checkbox" data-cfg="${k}"><i class="knob"></i></label>`;

    function createPanel(visible = true) {
        if (state.panel) { if (visible) togglePanel(true); return; }
        if (!mountRoot()) return;
        const p = document.createElement('section');
        p.className = 'panel';
        p.setAttribute('role', 'dialog');
        p.setAttribute('aria-label', 'AI Quiz Solver');
        p.innerHTML = `
        <header class="hd" id="drag">
            <div class="brand">
                <div class="logo">🤖</div>
                <div class="ttl"><b>AI Quiz Solver</b><small id="sub">v${VERSION} · chưa nhận diện quiz</small></div>
            </div>
            <div class="hbtns">
                <button class="ib" id="b-theme" title="Đổi giao diện: tự động / tối / sáng">◐</button>
                <button class="ib" id="b-min" title="Thu gọn">–</button>
                <button class="ib" id="b-x" title="Đóng">✕</button>
            </div>
        </header>
        <div class="bd">
            <div class="sum">
                <div class="ring">
                    <svg viewBox="0 0 64 64" aria-hidden="true"><circle class="trk" cx="32" cy="32" r="27"/><circle class="prg" id="ring" cx="32" cy="32" r="27"/></svg>
                    <div class="rt"><b id="r-pct">0%</b><small id="r-frac">0/0</small></div>
                </div>
                <div class="stats">
                    <div class="st"><b id="s-key">0</b><span><i class="k"></i>HTML</span></div>
                    <div class="st"><b id="s-ai">0</b><span><i class="a"></i>AI</span></div>
                    <div class="st"><b id="s-left">0</b><span><i class="n"></i>Chưa có</span></div>
                </div>
            </div>
            <div class="stat" id="status" data-k="info"><span class="si" id="s-ico">ℹ</span><span id="s-msg"></span></div>
            <div class="steps" id="steps" hidden>
                <div class="stp" data-s="1"><i>1</i><span>Gửi đề</span></div><div class="sbar"></div>
                <div class="stp" data-s="2"><i>2</i><span>Google AI</span></div><div class="sbar"></div>
                <div class="stp" data-s="3"><i>3</i><span>Nhận đáp án</span></div>
            </div>
            <div class="acts">
                <button class="btn pri" id="a-start">▶ Bắt đầu</button>
                <button class="btn" id="a-scan">⟳ Quét lại</button>
                <button class="btn ai" id="a-ask">🤖 Hỏi Google AI</button>
                <button class="btn" id="a-copy">📋 Copy prompt</button>
                <button class="btn ok" id="a-all" title="Chọn / điền đáp án đúng cho tất cả các câu đã có đáp án. Shift + bấm: chọn lại toàn bộ.">✓ Chọn tất cả đáp án</button>
            </div>
            <nav class="tabs" id="tabs">
                <button data-tab="list" class="on">Câu hỏi <em id="t-n">0</em></button>
                <button data-tab="ai">Google AI</button>
                <button data-tab="set">Cài đặt</button>
            </nav>

            <div class="pane" data-pane="list">
                <div class="seg" id="seg">
                    <button data-f="all" class="on">Tất cả<em id="c-all">0</em></button>
                    <button data-f="key">HTML<em id="c-key">0</em></button>
                    <button data-f="ai">AI<em id="c-ai">0</em></button>
                    <button data-f="none">Chưa có<em id="c-none">0</em></button>
                </div>
                <div class="list" id="list"></div>
            </div>

            <div class="pane" data-pane="ai" hidden>
                <div class="card">
                    <h4>Cách hoạt động</h4>
                    <div class="note">Câu có đáp án trong HTML được tick trực tiếp và <b>không</b> gửi đi. Các câu còn lại được gửi một lượt sang Google AI (AI Mode), script tự dán đề, tự đọc đáp án rồi đưa về panel này.</div>
                </div>
                <div class="two">
                    <button class="btn sm" id="a-open">↗ Mở Google AI</button>
                    <button class="btn sm" id="a-copy2">📋 Copy prompt</button>
                </div>
                <div class="card">
                    <h4>Tự động hoá</h4>
                    ${swHtml('autoAskAI', 'Tự hỏi AI khi bấm Bắt đầu', 'Câu chưa có đáp án trong HTML sẽ được gửi đi')}
                    ${swHtml('autoAskNew', 'Tự hỏi câu mới xuất hiện', 'Dành cho trang tải từng câu một')}
                    ${swHtml('aiAutoClick', 'Tự tick đáp án do AI trả lời', 'Tắt = chỉ hiện trong panel, bạn bấm Chọn mới tick')}
                    ${swHtml('aiAutoPaste', 'Tự dán đề và đọc kết quả', 'Tắt = chỉ mở Google AI, bạn dán tay')}
                    ${swHtml('aiTabActive', 'Tab Google AI hiện lên phía trước', 'Ổn định hơn chạy nền')}
                    ${swHtml('closeAITab', 'Tự đóng tab Google AI khi xong')}
                </div>
                <details class="card">
                    <summary>📥 Dán kết quả AI thủ công</summary>
                    <textarea class="tx" id="res" placeholder="Dán kết quả Google AI vào đây:&#10;1: B&#10;2: a=Đúng, b=Sai, c=Đúng, d=Sai&#10;3: 42"></textarea>
                    <div class="two" style="margin-top:7px">
                        <button class="btn sm" id="a-clear">Xoá</button>
                        <button class="btn sm pri" id="a-apply">✓ Đọc kết quả</button>
                    </div>
                </details>
            </div>

            <div class="pane" data-pane="set" hidden>
                <div class="card">
                    <h4>Tự động</h4>
                    ${swHtml('autoClick', 'Tự tick đáp án có sẵn trong HTML')}
                    ${swHtml('showNoteOnCard', 'Hiện ghi chú đáp án dưới mỗi câu', 'Ghi chú nhỏ ngay trên trang quiz')}
                </div>
                <div class="card">
                    <h4>Giao diện</h4>
                    <div class="seg" id="theme-seg" style="margin-top:4px">
                        <button data-theme-set="auto">Tự động</button>
                        <button data-theme-set="dark">Tối</button>
                        <button data-theme-set="light">Sáng</button>
                    </div>
                    <div class="note" style="margin-top:8px">Kéo tiêu đề để di chuyển panel, kéo nút tròn để đổi vị trí.</div>
                    <button class="btn sm" id="a-resetpos" style="width:100%;margin-top:8px">↺ Đặt lại vị trí</button>
                </div>
                <details class="card">
                    <summary>🎯 Selector riêng cho trang này</summary>
                    <input class="tx" id="s-card" placeholder="Khối mỗi câu hỏi (bắt buộc), vd .cau-hoi">
                    <input class="tx" id="s-question" placeholder="Nội dung câu hỏi, vd .noi-dung">
                    <input class="tx" id="s-option" placeholder="Từng đáp án (trắc nghiệm), vd .dap-an-item">
                    <input class="tx" id="s-statement" placeholder="Từng ý Đúng/Sai (nếu có)">
                    <input class="tx" id="s-input" placeholder="Ô điền đáp án ngắn (nếu có), vd input.tra-loi">
                    <input class="tx" id="s-answerKey" placeholder="Phần chứa đáp án đúng, vd .loi-giai">
                    <div class="two" style="margin-top:8px">
                        <button class="btn sm pri" id="s-save">Lưu và quét lại</button>
                        <button class="btn sm" id="s-clear">Xoá</button>
                    </div>
                </details>
                <div class="foot">v${VERSION} · <kbd>Ctrl</kbd>+<kbd>Shift</kbd>+<kbd>Q</kbd> mở/đóng panel</div>
            </div>
        </div>`;
        state.rootEl.appendChild(p);
        state.panel = p;

        // vị trí panel đã lưu
        const pos = store.get(PANEL_POS_KEY);
        if (pos && typeof pos.left === 'number' && typeof pos.top === 'number') {
            p.style.left = Math.min(Math.max(0, pos.left), innerWidth - 120) + 'px';
            p.style.top = Math.min(Math.max(0, pos.top), innerHeight - 56) + 'px';
            p.style.right = 'auto';
        }

        const $ = s => p.querySelector(s);
        const fields = ['card', 'question', 'option', 'statement', 'input', 'answerKey'];
        const fillFields = () => {
            const u = loadUserSel() || {};
            fields.forEach(f => { $('#s-' + f).value = u[f] || ''; });
        };
        fillFields();

        // công tắc
        p.querySelectorAll('[data-cfg]').forEach(cb => {
            cb.checked = !!CFG[cb.dataset.cfg];
            cb.addEventListener('change', () => { CFG[cb.dataset.cfg] = cb.checked; saveCfg(); });
        });

        // giao diện sáng/tối
        const paintThemeSeg = () => p.querySelectorAll('[data-theme-set]').forEach(b => b.classList.toggle('on', b.dataset.themeSet === CFG.theme));
        const setThemeCfg = t => { CFG.theme = t; saveCfg(); applyTheme(); paintThemeSeg(); };
        paintThemeSeg();
        p.querySelectorAll('[data-theme-set]').forEach(b => b.addEventListener('click', () => setThemeCfg(b.dataset.themeSet)));
        $('#b-theme').onclick = () => {
            const order = ['auto', 'dark', 'light'];
            const next = order[(order.indexOf(CFG.theme) + 1) % order.length];
            setThemeCfg(next);
            uiToast('Giao diện: ' + ({ auto: 'tự động theo hệ thống', dark: 'tối', light: 'sáng' })[next], 1600);
        };

        // kéo thả panel bằng thanh tiêu đề
        const head = $('#drag');
        let dx0 = 0, dy0 = 0, ox0 = 0, oy0 = 0, drag = false;
        head.addEventListener('pointerdown', e => {
            if (e.target.closest('button')) return;
            const r = p.getBoundingClientRect();
            drag = true; dx0 = e.clientX; dy0 = e.clientY; ox0 = r.left; oy0 = r.top;
            head.setPointerCapture(e.pointerId);
            head.classList.add('drag');
        });
        head.addEventListener('pointermove', e => {
            if (!drag) return;
            p.style.left = Math.min(Math.max(0, ox0 + e.clientX - dx0), innerWidth - 80) + 'px';
            p.style.top = Math.min(Math.max(0, oy0 + e.clientY - dy0), innerHeight - 56) + 'px';
            p.style.right = 'auto';
        });
        head.addEventListener('pointerup', e => {
            if (!drag) return;
            drag = false;
            head.classList.remove('drag');
            try { head.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
            const r = p.getBoundingClientRect();
            store.set(PANEL_POS_KEY, { left: r.left, top: r.top });
        });
        head.addEventListener('dblclick', e => { if (!e.target.closest('button')) p.classList.toggle('min'); });

        $('#b-min').onclick = () => p.classList.toggle('min');
        $('#b-x').onclick = () => togglePanel(false);

        // tab
        $('#tabs').addEventListener('click', e => {
            const b = e.target.closest('[data-tab]');
            if (b) setTab(b.dataset.tab);
        });

        // hành động chính
        $('#a-start').onclick = async () => {
            const ok = await onStart(true);
            if (!ok && !state.items.length) setStatus('Không tìm thấy quiz. Thử mở "Selector riêng" trong tab Cài đặt.', 'err');
        };
        $('#a-scan').onclick = async () => {
            const ok = scan(true);
            setStatus(ok ? `Tìm thấy ${state.items.length} câu (${state.mode}).` : 'Không tìm thấy quiz.', ok ? 'ok' : 'err');
            if (ok && state.started) await solveAllByKey();
        };
        $('#a-ask').onclick = () => {
            if (aiBusy()) { cancelAI(); return; }
            if (!state.items.length) scan(true);
            state.ai = null;
            askGoogleAI(false, false);
        };
        $('#a-all').onclick = e => selectAll(e.shiftKey);
        $('#a-copy').onclick = copyPrompt;
        $('#a-copy2').onclick = copyPrompt;
        $('#a-open').onclick = () => { openTab('https://www.google.com/search?udm=50'); setStatus('Đã mở Google AI. Dán prompt (đã copy) vào đó.', 'info'); };
        $('#a-clear').onclick = () => { $('#res').value = ''; };
        $('#a-apply').onclick = async () => {
            const ta = $('#res');
            if (!state.items.length) scan(true);
            const n = await applyAIResult(ta.value);
            if (n) { ta.value = ''; setStatus(`Đã đọc ${n} câu từ kết quả AI.`, 'ok'); setTab('list'); }
            else setStatus('Không đọc được. Mỗi câu cần một dòng dạng "1: B", "2: a=Đúng, b=Sai" hoặc "3: 42".', 'err');
        };

        // selector riêng
        $('#s-save').onclick = () => {
            const sel = {};
            fields.forEach(f => { sel[f] = $('#s-' + f).value.trim(); });
            if (!sel.card) { setStatus('Cần nhập selector của khối câu hỏi (card).', 'err'); return; }
            saveUserSel(sel);
            const ok = scan(true);
            setStatus(ok ? `Đã lưu. Tìm thấy ${state.items.length} câu (${state.mode}).` : 'Đã lưu nhưng selector chưa khớp câu nào.', ok ? 'ok' : 'warn');
        };
        $('#s-clear').onclick = () => {
            clearUserSel(); fillFields();
            scan(true);
            setStatus('Đã xoá selector riêng, quay về tự nhận diện.', 'info');
        };
        $('#a-resetpos').onclick = () => {
            store.del(PANEL_POS_KEY); store.del(POS_KEY);
            p.style.left = p.style.top = ''; p.style.right = '';
            if (state.launcher) { state.launcher.style.left = state.launcher.style.top = ''; state.launcher.style.right = state.launcher.style.bottom = ''; }
            uiToast('Đã đặt lại vị trí', 1500);
        };

        // lọc + danh sách
        $('#seg').addEventListener('click', e => {
            const b = e.target.closest('[data-f]');
            if (!b) return;
            state.filter = b.dataset.f;
            lastListHtml = '';
            render();
        });
        $('#list').addEventListener('click', e => {
            const row = e.target.closest('.q');
            if (!row) return;
            const it = state.items[Number(row.dataset.i)];
            if (!it) return;
            if (e.target.closest('[data-pick]')) {
                if (it.answer != null) { applied.delete(it.card); pick(it); }
                return;
            }
            if (e.target.closest('[data-exp]')) {
                if (state.open.has(it.fp)) state.open.delete(it.fp); else state.open.add(it.fp);
                lastListHtml = '';
                render();
                return;
            }
            it.card.scrollIntoView({ behavior: 'smooth', block: 'center' });
            it.card.classList.add('tm-ai-flash');
            setTimeout(() => it.card.classList.remove('tm-ai-flash'), 1500);
        });

        setTab(state.tab);
        paintStatus();
        paintStage();
        render();
        if (!visible) p.hidden = true;
        updateLauncher();
    }

    // ---------- vẽ lại danh sách / số liệu ----------
    let lastListHtml = '';
    const chipOf = it => it.type === 'mc' ? (it.multi ? 'Nhiều đáp án' : 'Trắc nghiệm') : it.type === 'tf' ? 'Đúng/Sai' : 'Điền ngắn';

    function pillsOf(it) {
        if (it.type === 'mc') return String(it.answer).split('').map(c => `<span class="pill">${esc(c)}</span>`).join('');
        if (it.type === 'tf') return Object.entries(it.answer).map(([k, v]) => `<span class="pill ${v ? 't' : 'f'}">${esc(k)} ${v ? 'Đ' : 'S'}</span>`).join('');
        return `<span class="pill txt" title="${esc(it.answer)}">${esc(String(it.answer).slice(0, 80))}</span>`;
    }

    function render() {
        updateLauncher();
        const p = state.panel;
        if (!p) return;
        const items = state.items;
        const total = items.length;
        const nKey = items.filter(i => i.source === 'answer-key').length;
        const nAI = items.filter(i => i.source === 'google-ai').length;
        const done = items.filter(i => i.solved).length;
        const left = total - done;
        const pct = total ? Math.round(done / total * 100) : 0;

        const set = (sel, v) => { const el = p.querySelector(sel); if (el && el.textContent !== String(v)) el.textContent = v; };
        set('#sub', `v${VERSION} · ` + (state.mode || 'chưa nhận diện quiz'));
        set('#r-pct', pct + '%');
        set('#r-frac', `${done}/${total}`);
        set('#s-key', nKey); set('#s-ai', nAI); set('#s-left', left);
        set('#t-n', total);
        set('#c-all', total); set('#c-key', nKey); set('#c-ai', nAI); set('#c-none', left);
        p.querySelector('#ring').style.strokeDashoffset = String(RING_C * (1 - (total ? done / total : 0)));

        const all = p.querySelector('#a-all');
        all.textContent = '✓ Chọn tất cả đáp án' + (done ? ` (${done})` : '');
        all.disabled = !done;

        const ask = p.querySelector('#a-ask');
        const busy = aiBusy();
        ask.textContent = busy ? '■ Dừng chờ AI' : '🤖 Hỏi Google AI';
        ask.classList.toggle('stop', busy);

        const f = state.filter;
        p.querySelectorAll('#seg [data-f]').forEach(b => b.classList.toggle('on', b.dataset.f === f));
        const show = it => f === 'all' ||
            (f === 'key' && it.source === 'answer-key') ||
            (f === 'ai' && it.source === 'google-ai') ||
            (f === 'none' && !it.solved);

        const html = items.map((it, i) => {
            if (!show(it)) return '';
            const ai = it.source === 'google-ai';
            const cls = it.solved ? (ai ? 'ai' : 'ok') : 'no';
            const q = esc(it.question.slice(0, 140)) + (it.question.length > 140 ? '…' : '');
            const waiting = !it.solved && busy && state.ai.map && Object.values(state.ai.map).includes(it.fp);
            const meta = `<span class="chip">${chipOf(it)}</span>` + (it.hasImg ? '<span class="chip w" title="Câu có hình, AI không nhìn thấy">⚠ có hình</span>' : '') +
                (it.solved
                    ? `<span class="src">${ai ? 'AI' : 'HTML'}</span>${pillsOf(it)}`
                    : waiting ? '<span class="wt"><i class="sp"></i>đang hỏi AI…</span>' : '<span class="mu">chưa có đáp án</span>');
            const open = ai && it.aiText && state.open.has(it.fp);
            return `<article class="q ${cls}" data-i="${i}">
                <div class="qn">${i + 1}</div>
                <div class="qb"><div class="qt">${q || '(không đọc được nội dung câu)'}</div><div class="qm">${meta}</div>
                    ${open ? `<div class="qx"><pre>${esc(it.aiText.trim())}</pre></div>` : ''}</div>
                <div class="qa">
                    ${it.solved ? `<button class="mini" data-pick title="Chọn / điền đáp án này trên trang">${it.type === 'sa' ? 'Điền' : 'Chọn'}</button>` : ''}
                    ${ai && it.aiText ? `<button class="mini ghost" data-exp title="Xem giải thích của AI">${open ? '▲' : '▼'}</button>` : ''}
                </div></article>`;
        }).join('') || `<div class="empty">${total ? 'Không có câu nào trong mục này.' : 'Chưa có câu nào. Bấm "Quét lại" nếu trang vừa tải xong.'}</div>`;

        if (html !== lastListHtml) {
            lastListHtml = html;
            p.querySelector('#list').innerHTML = html;
        }
    }

    // =========================================================
    // INIT
    // =========================================================
    function init() {
        if (window.__tmQuizV11) return;
        window.__tmQuizV11 = true;
        if (runAgent()) return; // tab Google AI do script mở: chỉ làm nhiệm vụ dán/đọc
        loadCfg();
        injectPageCSS();
        hookStartButton();

        // Ctrl + Shift + Q: mở/đóng panel
        document.addEventListener('keydown', e => {
            if (e.ctrlKey && e.shiftKey && e.code === 'KeyQ') {
                e.preventDefault();
                togglePanel();
            }
        });

        // giữ panel/nút trong màn hình khi đổi kích thước cửa sổ
        window.addEventListener('resize', () => {
            [state.panel, state.launcher].forEach(el => {
                if (!el || !el.style.left) return;
                const r = el.getBoundingClientRect();
                el.style.left = Math.min(Math.max(0, r.left), Math.max(0, innerWidth - Math.min(r.width, 120))) + 'px';
                el.style.top = Math.min(Math.max(0, r.top), Math.max(0, innerHeight - 56)) + 'px';
            });
        });
        try {
            matchMedia('(prefers-color-scheme: light)').addEventListener('change', applyTheme);
        } catch (e) { /* ignore */ }

        ensureUI();
        applyTheme();
        watch();
        schedule(300);

        if (window.__TM_DEBUG) {
            window.__tmQuiz = { state, CFG, detectItems, scan, solveAllByKey, buildPrompt, applyAIResult, askGoogleAI, parseResultLine, countResults, normResult, selectAll, togglePanel, render, createPanel, setStage, setStatus };
        }
    }

    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
})();