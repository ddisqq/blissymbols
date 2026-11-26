// Blissymbols in depth: a 3D reading of the Lean export.
//
// Inputs (both generated, see README):
//   BLISS3D_PATHS  geometry of the primitive paths (from blissdata_chars.js)
//   BLISS3D_DATA   every character flattened to primitive strokes, every word
//                  expanded to characters, and the Pauli–Jung sentences with
//                  their verdicts: all computed by Lean (pauli-jung/BlissExport.lean)
(function () {
  'use strict';
  var D = BLISS3D_DATA, PATHS = BLISS3D_PATHS;
  var UNIT = 1 / 64;          // world units per Bliss unit
  var STROKE = 4;             // tube radius in Bliss units (2D stroke width is 8)
  var QSPACE = 32;            // quarter-square gap between characters

  // ---------- theme ----------
  var css = function (name) {
    return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  };
  var theme = {};
  function readTheme() {
    ['paper', 'sheet', 'ink', 'muted', 'rule', 'meaning', 'cause', 'chance', 'plate'].forEach(function (k) {
      theme[k] = css('--' + k);
    });
  }

  // ---------- primitive paths -> 3D curves ----------
  // Points of an SVG-style circular arc (sweep flag 0), computed in SVG
  // coordinates (y down) because that is how the database defines its arcs.
  function arcPoints(x1, y1, x2, y2, r, large) {
    var sx1 = x1, sy1 = -y1, sx2 = x2, sy2 = -y2;
    var dx = (sx1 - sx2) / 2, dy = (sy1 - sy2) / 2;
    var d2 = dx * dx + dy * dy;
    if (r * r < d2) r = Math.sqrt(d2);
    var h = Math.sqrt(Math.max(0, r * r - d2) / d2);
    var sign = large ? 1 : -1;          // sweep = 0: '+' iff large-arc differs from sweep
    var cx = (sx1 + sx2) / 2 + sign * h * dy;
    var cy = (sy1 + sy2) / 2 - sign * h * dx;
    var a1 = Math.atan2(sy1 - cy, sx1 - cx), a2 = Math.atan2(sy2 - cy, sx2 - cx);
    var delta = a2 - a1;
    if (delta > 0) delta -= 2 * Math.PI;  // sweep = 0: angle decreases
    var n = Math.max(8, Math.ceil(Math.abs(delta) * 10)), pts = [];
    for (var i = 0; i <= n; i++) {
      var a = a1 + delta * i / n;
      pts.push([cx + r * Math.cos(a), -(cy + r * Math.sin(a))]);
    }
    return pts;
  }

  function v3(p) { return new THREE.Vector3(p[0] * UNIT, p[1] * UNIT, 0); }

  // Add one positioned primitive to a group.
  function addStroke(group, prim, ox, oy, mats) {
    var P = PATHS[prim], pts = null, closed = false;
    if (P.form === 'line') {
      pts = [[P.x1 + ox, P.y1 + oy], [P.x2 + ox, P.y2 + oy]];
    } else if (P.form === 'arc' || P.form === 'bigarc') {
      pts = arcPoints(P.x1 + ox, P.y1 + oy, P.x2 + ox, P.y2 + oy, P.rx, P.form === 'bigarc');
    } else if (P.form === 'quadratic') {
      pts = [];
      for (var i = 0; i <= 16; i++) {
        var t = i / 16, u = 1 - t;
        pts.push([u * u * P.x1 + 2 * u * t * P.qx + t * t * P.x2 + ox,
                  u * u * P.y1 + 2 * u * t * P.qy + t * t * P.y2 + oy]);
      }
    } else if (P.form === 'circle') {
      pts = []; closed = true;
      for (var k = 0; k < 40; k++) {
        var a = 2 * Math.PI * k / 40;
        pts.push([P.x + ox + P.r * Math.cos(a), P.y + oy + P.r * Math.sin(a)]);
      }
    } else if (P.form === 'dot' || P.form === 'disc') {
      var ball = new THREE.Mesh(new THREE.SphereGeometry((P.form === 'dot' ? 5 : P.r + 1) * UNIT, 16, 12), mats.ink);
      ball.position.set((P.x + ox) * UNIT, (P.y + oy) * UNIT, 0);
      group.add(ball);
      return;
    } else if (P.form === 'text') {
      group.add(textPlane(P.text, P.fontsize, (P.x + ox + P.w / 2), (oy + P.y - P.h), mats.color));
      return;
    } else {
      return;
    }
    var curve = pts.length === 2
      ? new THREE.LineCurve3(v3(pts[0]), v3(pts[1]))
      : new THREE.CatmullRomCurve3(pts.map(v3), closed, 'centripetal');
    group.add(new THREE.Mesh(new THREE.TubeGeometry(curve, Math.max(1, (pts.length - 1) * 2), STROKE * UNIT, 10, closed), mats.ink));
    if (!closed) {
      [pts[0], pts[pts.length - 1]].forEach(function (p) {
        var cap = new THREE.Mesh(new THREE.SphereGeometry(STROKE * UNIT, 10, 8), mats.ink);
        cap.position.copy(v3(p));
        group.add(cap);
      });
    }
  }

  // Letters and digits inside symbols: drawn on a small plane.
  function textPlane(text, fontsize, cx, baseline, color) {
    var px = 128, c = document.createElement('canvas');
    c.width = c.height = px;
    var g = c.getContext('2d');
    g.fillStyle = color;
    g.font = '500 ' + Math.round(px * 0.78) + 'px Arial, Helvetica, sans-serif';
    g.textAlign = 'center';
    g.textBaseline = 'alphabetic';
    g.fillText(text, px / 2, px * 0.8);
    var tex = new THREE.CanvasTexture(c);
    var size = fontsize / 0.78;
    var mesh = new THREE.Mesh(new THREE.PlaneGeometry(size * UNIT, size * UNIT),
      new THREE.MeshBasicMaterial({ map: tex, transparent: true, side: THREE.DoubleSide, depthWrite: false }));
    mesh.position.set(cx * UNIT, (baseline + size * 0.3) * UNIT, 0);
    return mesh;
  }

  // ---------- symbols ----------
  function charsOf(name) {
    if (D.words[name]) return D.words[name].map(function (i) { return D.charNames[i]; });
    if (D.glyphs[name]) return [name];
    return null;
  }

  // A character or word as a group centred on x, standing on y = 0.
  // Indicators sit above the character before them; no kerning.
  function buildSymbol(name, color) {
    var names = charsOf(name);
    if (!names) return null;
    var mats = { color: color, ink: new THREE.MeshStandardMaterial({ color: color, roughness: 0.55, metalness: 0.05 }) };
    var group = new THREE.Group(), x = 0, prev = null, top = 0;
    names.forEach(function (ch) {
      var g = D.glyphs[ch], w = g.w / 1000, h = g.h / 1000, cx, cy = 0;
      if (ch.slice(0, 10) === 'indicator_' && prev) {
        cx = prev.x + (prev.w - w) / 2;
        cy = Math.max(0, prev.h - 192);
      } else {
        if (prev) x += QSPACE;
        cx = x; x += w; prev = { x: cx, w: w, h: h };
      }
      top = Math.max(top, h + cy);
      g.s.forEach(function (s) { addStroke(group, s[0], cx + s[1] / 1000, cy + s[2] / 1000, mats); });
    });
    group.children.forEach(function (m) { m.position.x -= x * UNIT / 2; });
    group.userData = { width: x * UNIT, height: Math.max(top, 256) * UNIT };
    return group;
  }

  // ---------- scene ----------
  var canvas = document.getElementById('scene');
  var renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true, alpha: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  var scene = new THREE.Scene();
  var camera = new THREE.PerspectiveCamera(32, 1.6, 0.1, 200);
  var hemi = new THREE.HemisphereLight(0xffffff, 0x8899aa, 0.85);
  var sun = new THREE.DirectionalLight(0xffffff, 0.75);
  sun.position.set(4, 8, 10);
  scene.add(hemi, sun);
  var content = new THREE.Group();
  scene.add(content);

  var HOME = { theta: 0.5, phi: 0.16, dist: 24 };
  var orbit = { theta: HOME.theta, phi: HOME.phi, dist: HOME.dist };
  var reduce = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  var turning = !reduce, t0 = performance.now(), dragging = false;

  function placeCamera() {
    var c = Math.cos(orbit.phi);
    camera.position.set(orbit.dist * Math.sin(orbit.theta) * c, orbit.dist * Math.sin(orbit.phi) + 1.1, orbit.dist * Math.cos(orbit.theta) * c);
    camera.lookAt(0, 1.1, 0);
  }

  function resize() {
    var w = canvas.clientWidth, h = canvas.clientHeight;
    if (!w || !h) return;
    renderer.setSize(w, h, false);
    camera.aspect = w / h;
    camera.fov = w / h < 1.2 ? 46 : 32;
    camera.updateProjectionMatrix();
  }

  function clearContent() {
    content.traverse(function (o) {
      if (o.geometry) o.geometry.dispose();
      if (o.material) { if (o.material.map) o.material.map.dispose(); o.material.dispose(); }
    });
    while (content.children.length) content.remove(content.children[0]);
  }

  function label(text, color) {
    var c = document.createElement('canvas');
    c.width = 512; c.height = 64;
    var g = c.getContext('2d');
    g.fillStyle = color;
    g.font = '500 30px "IBM Plex Mono", ui-monospace, Menlo, monospace';
    g.textAlign = 'center'; g.textBaseline = 'middle';
    g.fillText(text.toUpperCase().split('').join(' '), 256, 34);
    var mesh = new THREE.Mesh(new THREE.PlaneGeometry(5.6, 0.7),
      new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(c), transparent: true, side: THREE.DoubleSide, depthWrite: false }));
    return mesh;
  }

  // One of the two aspect sheets.
  function plate(w, h) {
    var g = new THREE.Group();
    var geo = new THREE.PlaneGeometry(w, h);
    g.add(new THREE.Mesh(geo, new THREE.MeshBasicMaterial({ color: theme.plate, transparent: true, opacity: 0.16, side: THREE.DoubleSide, depthWrite: false })));
    g.add(new THREE.LineSegments(new THREE.EdgesGeometry(geo), new THREE.LineBasicMaterial({ color: theme.plate })));
    return g;
  }

  function tubeBetween(a, b, radius, color, opacity) {
    var mat = new THREE.MeshStandardMaterial({ color: color, roughness: 0.5, transparent: opacity < 1, opacity: opacity });
    return new THREE.Mesh(new THREE.TubeGeometry(new THREE.LineCurve3(a, b), 1, radius, 10, false), mat);
  }

  var BASE = -2.6, DEPTH = 1.9, SIDE = 3.5;

  function showSentence(s) {
    clearContent();
    var kind = s.sync ? 'meaning' : (s.linked ? 'cause' : 'chance');
    var mental = buildSymbol(s.mental, theme.ink), physical = buildSymbol(s.physical, theme.ink);
    var link = buildSymbol(s.link, theme[kind]), arch = buildSymbol(s.archetype, s.meaningful ? theme.ink : theme.rule);

    mental.position.set(-SIDE, BASE, DEPTH);
    physical.position.set(SIDE, BASE, -DEPTH);
    var pm = plate(5.6, 6.4), pp = plate(5.6, 6.4);
    pm.position.set(-SIDE, BASE + 2.7, DEPTH - 0.25);
    pp.position.set(SIDE, BASE + 2.7, -DEPTH - 0.25);
    var lm = label('mind', theme.muted), lp = label('matter', theme.muted), la = label('archetype', theme.muted);
    lm.position.set(-SIDE, BASE - 0.95, DEPTH);
    lp.position.set(SIDE, BASE - 0.95, -DEPTH);

    link.scale.setScalar(0.55);
    link.position.set(0, BASE + 0.2, 0);
    arch.scale.setScalar(0.62);
    var archY = BASE + 6.2;
    arch.position.set(0, archY, 0);
    la.position.set(0, archY + 2.95, 0);
    content.add(pm, pp, mental, physical, link, arch, lm, lp, la);

    var mTop = new THREE.Vector3(-SIDE, BASE + mental.userData.height + 0.3, DEPTH);
    var pTop = new THREE.Vector3(SIDE, BASE + physical.userData.height + 0.3, -DEPTH);
    var aLeft = new THREE.Vector3(-arch.userData.width * 0.31 - 0.3, archY + 1.2, 0);
    var aRight = new THREE.Vector3(arch.userData.width * 0.31 + 0.3, archY + 1.2, 0);
    if (s.meaningful) {
      // Meaning descends from the archetype to both aspects.
      var c = s.sync ? theme.meaning : theme.rule;
      content.add(tubeBetween(aLeft, mTop, 0.03, c, 1), tubeBetween(aRight, pTop, 0.03, c, 1));
    }
    if (s.linked) {
      // A causal link runs through the depth between the sheets.
      var a = new THREE.Vector3(-SIDE + mental.userData.width / 2 + 0.4, BASE + 2.2, DEPTH);
      var b = new THREE.Vector3(SIDE - physical.userData.width / 2 - 0.4, BASE + 2.2, -DEPTH);
      content.add(tubeBetween(a, b, 0.07, theme.cause, 1));
    }
  }

  function showSymbol(name) {
    var sym = buildSymbol(name, theme.ink);
    if (!sym) return false;
    clearContent();
    var scale = Math.min(1.9, 11 / Math.max(sym.userData.width, 2.5));
    sym.scale.setScalar(scale);
    sym.position.set(0, -2.5 * scale + 0.4, 0);
    content.add(sym);
    return true;
  }

  // ---------- page ----------
  var current = { kind: 'sentence', index: 0 };
  var listEl = document.getElementById('caseList');
  var verdictEl = document.getElementById('verdict');
  var sentenceEl = document.getElementById('sentence');
  var noteEl = document.getElementById('symbolNote');
  var WORDS = { meaning: 'meaning', cause: 'cause', chance: 'chance' };
  var VERDICTS = {
    meaning: 'Synchronicity: joined by meaning, with no causal link.',
    cause: 'Causally linked, so not a synchronicity.',
    chance: 'Neither linked nor meaningful: a run of chance.'
  };
  function kindOf(s) { return s.sync ? 'meaning' : (s.linked ? 'cause' : 'chance'); }

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  function renderPanel() {
    Array.prototype.forEach.call(listEl.querySelectorAll('button'), function (b, i) {
      b.setAttribute('aria-current', current.kind === 'sentence' && i === current.index ? 'true' : 'false');
    });
    sentenceEl.textContent = '';
    if (current.kind === 'sentence') {
      var s = D.sentences[current.index], k = kindOf(s);
      verdictEl.className = 'verdict ' + k;
      verdictEl.textContent = s.title + '. ' + VERDICTS[k];
      [['Mind', s.mental], ['Link', s.link], ['Matter', s.physical], ['Archetype', s.archetype]].forEach(function (p) {
        var d = el('div');
        d.appendChild(el('span', 'label', p[0]));
        d.appendChild(el('code', null, p[1]));
        sentenceEl.appendChild(d);
      });
    } else {
      var chars = charsOf(current.name);
      verdictEl.className = 'verdict';
      verdictEl.textContent = current.name;
      var d = el('div');
      d.appendChild(el('span', 'label', chars.length > 1 ? 'Word of ' + chars.length + ' characters' : 'Character'));
      d.appendChild(el('code', null, chars.join('  +  ')));
      d.style.gridColumn = '1 / -1';
      sentenceEl.appendChild(d);
    }
  }

  function show() {
    readTheme();
    if (current.kind === 'sentence') showSentence(D.sentences[current.index]);
    else showSymbol(current.name);
    renderPanel();
  }

  D.sentences.forEach(function (s, i) {
    var li = el('li'), b = el('button'), k = kindOf(s);
    b.type = 'button';
    b.appendChild(el('span', null, s.title));
    b.appendChild(el('span', 'chip ' + k, WORDS[k]));
    b.addEventListener('click', function () { current = { kind: 'sentence', index: i }; show(); });
    li.appendChild(b);
    listEl.appendChild(li);
  });

  var input = document.getElementById('symbolInput'), dl = document.getElementById('symbolNames');
  var allNames = D.charNames.concat(Object.keys(D.words));
  input.addEventListener('input', function () {
    var q = input.value.trim().toLowerCase();
    dl.textContent = '';
    if (q.length < 2) return;
    var n = 0;
    for (var i = 0; i < allNames.length && n < 40; i++) {
      if (allNames[i].toLowerCase().indexOf(q) >= 0) {
        var o = document.createElement('option'); o.value = allNames[i]; dl.appendChild(o); n++;
      }
    }
  });
  function trySymbol() {
    var q = input.value.trim();
    if (!q) return;
    var name = charsOf(q) ? q : null;
    if (!name) {
      var low = q.toLowerCase();
      name = allNames.filter(function (n) { return n.toLowerCase().split(/[,_()\-]+/).indexOf(low) >= 0; })[0] ||
             allNames.filter(function (n) { return n.toLowerCase().indexOf(low) >= 0; })[0];
    }
    if (!name) { noteEl.textContent = 'No symbol named “' + q + '” in the set.'; return; }
    noteEl.textContent = name === q ? '' : 'Showing ' + name;
    current = { kind: 'symbol', name: name };
    show();
  }
  document.getElementById('showSymbol').addEventListener('click', trySymbol);
  input.addEventListener('keydown', function (e) { if (e.key === 'Enter') trySymbol(); });
  input.addEventListener('change', function () { if (charsOf(input.value.trim())) trySymbol(); });

  var c = D.counts;
  document.getElementById('proof').innerHTML =
    'Checked in Lean 4: the set’s ' + c.chars.toLocaleString() + ' characters are built from ' +
    (c.items - c.chars).toLocaleString() + ' shapes and ' + c.prims + ' primitive paths with no missing or circular reference ' +
    '(<code>Bliss.items_wf</code>), and likewise its ' + c.words.toLocaleString() + ' words (<code>Bliss.words_wf</code>). ' +
    'The strokes drawn here are the output of <code>Bliss.flatten</code>. In each sentence the link symbol says “meaning” ' +
    'exactly when the pair is a synchronicity in its model (<code>link_is_meaning_iff</code>). ' +
    'Which symbols stand for which event, and which causes each model contains, are choices made by hand.';

  // ---------- interaction ----------
  var last = null;
  canvas.addEventListener('pointerdown', function (e) { dragging = true; last = [e.clientX, e.clientY]; canvas.setPointerCapture(e.pointerId); });
  canvas.addEventListener('pointermove', function (e) {
    if (!dragging) return;
    orbit.theta -= (e.clientX - last[0]) * 0.008;
    orbit.phi = Math.max(-1.2, Math.min(1.2, orbit.phi + (e.clientY - last[1]) * 0.006));
    last = [e.clientX, e.clientY];
    setTurning(false);
  });
  ['pointerup', 'pointercancel'].forEach(function (n) { canvas.addEventListener(n, function () { dragging = false; }); });
  canvas.addEventListener('wheel', function (e) {
    e.preventDefault();
    orbit.dist = Math.max(8, Math.min(60, orbit.dist * (e.deltaY > 0 ? 1.08 : 0.93)));
  }, { passive: false });

  var spinBtn = document.getElementById('spin');
  function setTurning(on) {
    turning = on;
    if (on) t0 = performance.now() - Math.asin(Math.max(-1, Math.min(1, orbit.theta / 0.6))) * 2600;
    spinBtn.setAttribute('aria-pressed', on ? 'true' : 'false');
    spinBtn.textContent = on ? 'Pause turning' : 'Turn slowly';
  }
  spinBtn.addEventListener('click', function () { setTurning(!turning); });
  document.getElementById('reset').addEventListener('click', function () {
    orbit.theta = HOME.theta; orbit.phi = HOME.phi; orbit.dist = HOME.dist;
    setTurning(false);
  });
  setTurning(turning);

  if (window.ResizeObserver) new ResizeObserver(resize).observe(canvas);
  window.addEventListener('resize', resize);
  if (window.matchMedia) {
    var mq = window.matchMedia('(prefers-color-scheme: dark)');
    if (mq.addEventListener) mq.addEventListener('change', show);
  }
  new MutationObserver(show).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });

  function frame(now) {
    // A slow swing, not a full spin: the symbols stay readable from the front.
    if (turning && !dragging) orbit.theta = 0.6 * Math.sin((now - t0) / 2600);
    placeCamera();
    renderer.render(scene, camera);
    requestAnimationFrame(frame);
  }
  resize();
  show();
  if (!turning) orbit.theta = HOME.theta;
  requestAnimationFrame(frame);
})();
