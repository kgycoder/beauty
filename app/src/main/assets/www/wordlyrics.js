/* ════════════════════════════════════════════════════════════════════
   WORD-SYNC LYRICS ENGINE  (Apple Music 스타일 단어/음절 싱크)
   ────────────────────────────────────────────────────────────────────
   · 글자 내부를 따라 빛이 흐르듯 채워지는 그라디언트 스윕 (단어별 길이·타임스탬프에 따라 속도가 달라진다)
   · 진행 중인 단어는 부드럽게 들어올려지고(lift), 지나간 단어는 들어올려진 채 유지, 줄이 끝나면 내려온다
   · 오래 끄는 단어는 빛나는 글로우
   · 공백·문장부호는 Java 쪽(WordLyrics.cleanWords)에서 인접 단어에 병합되어 하이라이트가 끊기거나 튀지 않는다

   성능 설계
   · 줄 전체가 아니라 "지금 재생 중인 줄의 아직 끝나지 않은 단어 몇 개"만 매 프레임 갱신한다.
   · 값은 양자화해 바뀔 때만 style 에 쓴다 (스타일 무효화 최소화). 레이아웃(reflow)을 일으키는 속성은 쓰지 않는다.
   · rAF 루프는 "재생 중 + 단어 싱크 줄이 활성"일 때만 돈다. 일시정지·백그라운드·줄 없음 → 즉시 정지(발열/배터리).
   · 프레임이 느린 기기(평균 >26ms)에서는 자동으로 30fps 로 낮춘다.
   · 비활성 줄은 일반 텍스트(색상만)로 그려져 background-clip:text / 변형 비용이 전혀 없다.
════════════════════════════════════════════════════════════════════ */
(function () {
    'use strict';

    const CJK_RE = /[\u3040-\u30ff\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]/;   // 한글은 띄어쓰기 단위라 제외
    const FILL_STEPS = 200, LIFT_STEPS = 40, GLOW_STEPS = 20;
    const GLOW_TAIL = 0.5;                                                    // 단어가 끝난 뒤 글로우가 사라지는 시간(초)

    const WS = {
        line: null, idx: -1, hosts: [], segs: [], W: null, n: 0,
        P: null, L: null, G: null, ptr: 0,
        raf: 0, lastT: -1, lastF: 0, ema: 16.7, skip: 0
    };

    /* ── 재생 시계: 플레이어 시간 샘플(갱신이 거칠 수 있음)을 프레임 단위로 부드럽게 보간 ── */
    const C = { ok: false, m: 0, p: 0, s: -1 };
    function _clock(now) {
        const s = getPlayheadTime();
        if (!S.playing) { C.ok = false; return s; }
        if (!C.ok) { C.ok = true; C.m = s; C.p = now; C.s = s; return s; }
        let m = C.m + (now - C.p) / 1000;
        if (s !== C.s) {                       // 새 샘플이 들어왔을 때만 보정 (같은 값이면 순수 외삽)
            C.s = s;
            const err = s - m;
            m = Math.abs(err) > 0.3 ? s : m + err * 0.4;
        }
        C.m = m; C.p = now;
        return m;
    }

    /* ── DOM 구성 ──────────────────────────────────────────────── */
    function _prep(line) {
        if (line._wsPrep) return;
        const W = line.words;
        const d = W.map(w => w.e - w.s).sort((a, b) => a - b);
        const med = d[d.length >> 1] || 0.3;
        for (const w of W) {
            const dur = w.e - w.s;
            w.gl = dur >= 0.9 || (dur >= 0.55 && dur >= med * 2);          // 다른 단어보다 오래 머무는 단어
        }
        line._wsPrep = true;
    }

    function build(el, line) {
        const W = line.words;
        if (!W || !W.length) return false;
        _prep(line);
        el.textContent = '';
        const wrap = document.createElement('span');
        wrap.className = 'ws-wrap';
        const segs = new Array(W.length);
        let grp = null;
        for (let k = 0; k < W.length; k++) {
            const w = W[k];
            const m = /^(\s*)([\s\S]*?)(\s*)$/.exec(w.t);
            const lead = m[1], core = m[2], trail = m[3];
            if (lead) { grp = null; wrap.appendChild(document.createTextNode(lead)); }
            const sp = document.createElement('span');
            sp.className = w.gl ? 'ws-w ws-gl' : 'ws-w';
            sp.textContent = core || w.t;
            const cjk = CJK_RE.test(core);
            if (!grp || cjk) { grp = document.createElement('span'); grp.className = 'ws-g'; wrap.appendChild(grp); }
            grp.appendChild(sp);
            segs[k] = sp;
            if (trail) { grp = null; wrap.appendChild(document.createTextNode(trail)); }
            else if (cjk) grp = null;
        }
        el.appendChild(wrap);
        el.classList.add('ws-line');
        el._ws = { segs };
        return true;
    }

    /* ── 단어 하나의 상태 계산/반영 ─────────────────────────────── */
    function _set(k, name, v) {
        const segs = WS.segs;
        for (let h = 0; h < segs.length; h++) segs[h][k].style.setProperty(name, v);
    }

    /* 반환: 이 단어가 완전히 끝났는지(최종값까지 기록됨) */
    function _paint(k, t) {
        const w = WS.W[k];
        const dur = Math.max(0.04, w.e - w.s);

        // 채움: 길이·타임스탬프에 따른 속도 + 완만한 가감속(기계적인 등속 느낌 제거)
        let p = (t - w.s) / dur;
        p = p < 0 ? 0 : p > 1 ? 1 : p;
        p = p * 0.7 + p * p * (3 - 2 * p) * 0.3;
        const pq = Math.round(p * FILL_STEPS);
        if (pq !== WS.P[k]) { WS.P[k] = pq; _set(k, '--p', pq / FILL_STEPS); }

        // 들어올림: 단어가 시작되면 부드럽게 올라가 유지
        const ld = dur * 0.8 < 0.28 ? 0.28 : dur * 0.8 > 0.65 ? 0.65 : dur * 0.8;
        let x = (t - w.s) / ld;
        x = x < 0 ? 0 : x > 1 ? 1 : x;
        x = x * x * (3 - 2 * x);
        const lq = Math.round(x * LIFT_STEPS);
        if (lq !== WS.L[k]) { WS.L[k] = lq; _set(k, '--l', lq / LIFT_STEPS); }

        let tail = 0;
        if (w.gl) {                                                          // 글로우: 시작 시 차오르고, 끝난 뒤 서서히 사라짐
            let g;
            if (t <= w.s) g = 0;
            else if (t < w.e) { const r = Math.min(0.35, dur * 0.35); g = Math.min(1, (t - w.s) / r); g = g * g * (3 - 2 * g); }
            else { g = 1 - Math.min(1, (t - w.e) / GLOW_TAIL); g = g * g * (3 - 2 * (g)); }
            const gq = Math.round(g * GLOW_STEPS);
            if (gq !== WS.G[k]) {
                const was = WS.G[k] > 0;
                WS.G[k] = gq;
                _set(k, '--g', gq / GLOW_STEPS);
                if ((gq > 0) !== was) for (let h = 0; h < WS.segs.length; h++) WS.segs[h][k].classList.toggle('ws-gon', gq > 0);
            }
            tail = GLOW_TAIL;
        }
        return t >= w.s + Math.max(dur, ld) + tail + 0.02;
    }

    function _fullPaint(t) {
        let ptr = -1;
        for (let k = 0; k < WS.n; k++) {
            const done = _paint(k, t);
            if (!done && ptr < 0) ptr = k;
        }
        WS.ptr = ptr < 0 ? WS.n : ptr;
        WS.lastT = t;
    }

    /* ── 프레임 루프 ────────────────────────────────────────────── */
    function _frame(now) {
        WS.raf = 0;
        if (!WS.line || !S.playing || window.__bgMode) return;
        const dt = now - WS.lastF; WS.lastF = now;
        if (dt > 0 && dt < 250) WS.ema = WS.ema * 0.9 + dt * 0.1;
        WS.raf = requestAnimationFrame(_frame);
        if (WS.ema > 26 && (WS.skip ^= 1)) return;                           // 느린 기기: 30fps

        const t = _clock(now);
        if (t < WS.lastT - 0.12 || t > WS.lastT + 0.6) { _fullPaint(t); return; }   // 시크
        const W = WS.W, n = WS.n;
        for (let k = WS.ptr; k < n; k++) {
            if (W[k].s > t) break;
            if (_paint(k, t) && k === WS.ptr) WS.ptr++;         // 끝난 단어는 최종값을 기록한 뒤 더 이상 건드리지 않는다
        }
        WS.lastT = t;
    }

    function _start() {
        if (WS.raf || !WS.line || !S.playing || window.__bgMode) return;
        C.ok = false;
        WS.lastF = performance.now();
        WS.raf = requestAnimationFrame(_frame);
    }
    function _stop() { if (WS.raf) { cancelAnimationFrame(WS.raf); WS.raf = 0; } }

    /* ── 활성 줄 전환 (_highlightLine / Lv / Fs / Ls 에서 호출. 같은 줄·같은 호스트면 아무것도 안 함) ── */
    function activate(idx) {
        const line = idx >= 0 ? LY.lines[idx] : null;
        const hosts = [];
        if (line && line.words) {
            const keys = ['el', 'el_lv', 'el_fs', 'el_ls'];
            for (let i = 0; i < 4; i++) {
                const e = line[keys[i]];
                if (e && e._ws && e.isConnected) hosts.push(e);
            }
        }
        if (line === WS.line && hosts.length === WS.hosts.length && hosts.every((h, i) => h === WS.hosts[i])) return;
        _deactivate();
        if (!line || !hosts.length) return;

        WS.line = line; WS.idx = idx; WS.hosts = hosts;
        WS.segs = hosts.map(h => h._ws.segs);
        WS.W = line.words; WS.n = line.words.length;
        WS.P = new Int16Array(WS.n).fill(-1);
        WS.L = new Int16Array(WS.n).fill(-1);
        WS.G = new Int16Array(WS.n).fill(-1);
        for (const h of hosts) h.classList.add('ws-on');
        C.ok = false;
        _fullPaint(S.playing ? _clock(performance.now()) : getPlayheadTime());
        _start();
    }

    function _deactivate() {
        _stop();
        for (const h of WS.hosts) h.classList.remove('ws-on');
        for (const sg of WS.segs) for (const sp of sg) if (sp.classList.contains('ws-gon')) sp.classList.remove('ws-gon');
        WS.line = null; WS.idx = -1; WS.hosts = []; WS.segs = []; WS.W = null; WS.n = 0; WS.ptr = 0;
    }

    /* 가사 틱(40ms)에서 호출: 재생이 다시 시작되면 루프 재개, 일시정지 중 시크하면 한 번 다시 그림 */
    function poke() {
        if (!WS.line) return;
        if (S.playing) { if (!WS.raf) _start(); return; }
        const t = getPlayheadTime();
        if (Math.abs(t - WS.lastT) > 0.03) _fullPaint(t);
    }

    document.addEventListener('visibilitychange', () => { if (document.hidden) _stop(); else _start(); });

    window.WS = { build, activate, poke, reset: _deactivate };
})();
