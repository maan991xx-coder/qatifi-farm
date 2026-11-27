/*
 * Bellavista HDR — دمج الإضاءات (Exposure Fusion, Mertens et al. 2007)
 * يشتغل داخل المتصفح بالكامل: ما في رفع للصور ولا أي خدمة خارجية.
 * Works as a Web Worker (postMessage) and as a Node module (for tests).
 */
(function () {
  var K = [0.0625, 0.25, 0.375, 0.25, 0.0625];

  function blur(src, w, h) {
    var tmp = new Float32Array(w * h), out = new Float32Array(w * h);
    var x, y, k, s, xx, yy, row;
    for (y = 0; y < h; y++) {
      row = y * w;
      for (x = 0; x < w; x++) {
        s = 0;
        for (k = -2; k <= 2; k++) {
          xx = x + k;
          if (xx < 0) xx = -xx; else if (xx >= w) xx = 2 * w - 2 - xx;
          if (xx < 0) xx = 0;
          s += K[k + 2] * src[row + xx];
        }
        tmp[row + x] = s;
      }
    }
    for (y = 0; y < h; y++) {
      for (x = 0; x < w; x++) {
        s = 0;
        for (k = -2; k <= 2; k++) {
          yy = y + k;
          if (yy < 0) yy = -yy; else if (yy >= h) yy = 2 * h - 2 - yy;
          if (yy < 0) yy = 0;
          s += K[k + 2] * tmp[yy * w + x];
        }
        out[y * w + x] = s;
      }
    }
    return out;
  }

  function down(src, w, h) {
    var b = blur(src, w, h);
    var nw = (w + 1) >> 1, nh = (h + 1) >> 1, d = new Float32Array(nw * nh);
    for (var y = 0; y < nh; y++) for (var x = 0; x < nw; x++) d[y * nw + x] = b[(2 * y) * w + 2 * x];
    return d;
  }

  function up(src, sw, w, h) {
    var o = new Float32Array(w * h);
    for (var y = 0; y < h; y++) {
      var r = (y >> 1) * sw, ro = y * w;
      for (var x = 0; x < w; x++) o[ro + x] = src[r + (x >> 1)];
    }
    return blur(o, w, h);
  }

  function sizes(w, h, L) {
    var s = [[w, h]];
    for (var i = 1; i < L; i++) s.push([(s[i - 1][0] + 1) >> 1, (s[i - 1][1] + 1) >> 1]);
    return s;
  }

  function gaussPyr(img, sz) {
    var p = [img];
    for (var i = 1; i < sz.length; i++) p.push(down(p[i - 1], sz[i - 1][0], sz[i - 1][1]));
    return p;
  }

  /**
   * imgs: array of RGBA Uint8ClampedArray (same w,h)
   * returns RGBA Uint8ClampedArray
   */
  function fuse(imgs, w, h, progress) {
    progress = progress || function () {};
    var N = imgs.length, n = w * h, i, p, j;
    var L = 1, m = Math.min(w, h);
    while (m >= 16 && L < 12) { m >>= 1; L++; }
    var sz = sizes(w, h, L);
    var steps = N * 2 + 2, done = 0;
    function tick(label) { done++; progress(done / steps, label); }

    // 1) weights: contrast * saturation * well-exposedness
    var W = [];
    for (i = 0; i < N; i++) {
      var a = imgs[i], gray = new Float32Array(n), wt = new Float32Array(n);
      for (p = 0, j = 0; p < n; p++, j += 4) gray[p] = (0.299 * a[j] + 0.587 * a[j + 1] + 0.114 * a[j + 2]) / 255;
      for (var y = 0; y < h; y++) {
        for (var x = 0; x < w; x++) {
          p = y * w + x; j = p * 4;
          var c = gray[p] * 4
            - gray[y * w + (x > 0 ? x - 1 : x + 1)]
            - gray[y * w + (x < w - 1 ? x + 1 : x - 1)]
            - gray[(y > 0 ? y - 1 : y + 1) * w + x]
            - gray[(y < h - 1 ? y + 1 : y - 1) * w + x];
          c = Math.abs(c);
          var r = a[j] / 255, g = a[j + 1] / 255, b = a[j + 2] / 255;
          var mu = (r + g + b) / 3;
          var s = Math.sqrt(((r - mu) * (r - mu) + (g - mu) * (g - mu) + (b - mu) * (b - mu)) / 3);
          var e = Math.exp(-((r - 0.5) * (r - 0.5) + (g - 0.5) * (g - 0.5) + (b - 0.5) * (b - 0.5)) / 0.08);
          wt[p] = (c + 0.02) * (s + 0.02) * e + 1e-12;
        }
      }
      W.push(wt);
      tick('weights');
    }
    for (p = 0; p < n; p++) {
      var sum = 0;
      for (i = 0; i < N; i++) sum += W[i][p];
      for (i = 0; i < N; i++) W[i][p] /= sum;
    }
    tick('normalize');

    // 2) blend Laplacian pyramids
    var R = [[], [], []], l, ch;
    for (ch = 0; ch < 3; ch++) for (l = 0; l < L; l++) R[ch].push(new Float32Array(sz[l][0] * sz[l][1]));
    for (i = 0; i < N; i++) {
      var gw = gaussPyr(W[i], sz);
      W[i] = null;
      for (ch = 0; ch < 3; ch++) {
        var src = imgs[i], plane = new Float32Array(n);
        for (p = 0, j = ch; p < n; p++, j += 4) plane[p] = src[j] / 255;
        var gp = gaussPyr(plane, sz);
        for (l = 0; l < L; l++) {
          var lw = sz[l][0], lh = sz[l][1], lap = gp[l], acc = R[ch][l], wl = gw[l], q;
          if (l < L - 1) {
            var u = up(gp[l + 1], sz[l + 1][0], lw, lh);
            for (q = 0; q < lw * lh; q++) acc[q] += wl[q] * (lap[q] - u[q]);
          } else {
            for (q = 0; q < lw * lh; q++) acc[q] += wl[q] * lap[q];
          }
        }
      }
      tick('blend');
    }

    // 3) collapse
    var outF = [];
    for (ch = 0; ch < 3; ch++) {
      var cur = R[ch][L - 1];
      for (l = L - 2; l >= 0; l--) {
        var uu = up(cur, sz[l + 1][0], sz[l][0], sz[l][1]), rl = R[ch][l];
        for (var t = 0; t < uu.length; t++) uu[t] += rl[t];
        cur = uu;
      }
      outF.push(cur);
    }

    // 4) gentle auto-levels (0.3% / 99.7% luminance) + slight saturation lift
    var hist = new Uint32Array(1024);
    for (p = 0; p < n; p++) {
      var lum = 0.299 * outF[0][p] + 0.587 * outF[1][p] + 0.114 * outF[2][p];
      var bi = Math.max(0, Math.min(1023, Math.round(lum * 1023)));
      hist[bi]++;
    }
    var lo = 0, hi = 1023, accn = 0;
    for (lo = 0; lo < 1023; lo++) { accn += hist[lo]; if (accn > n * 0.003) break; }
    accn = 0;
    for (hi = 1023; hi > 0; hi--) { accn += hist[hi]; if (accn > n * 0.003) break; }
    var blk = Math.min(lo / 1023, 0.08), wht = Math.max(hi / 1023, 0.85);
    var sc = 1 / Math.max(0.05, wht - blk), SAT = 1.08;
    var out = new Uint8ClampedArray(n * 4);
    for (p = 0, j = 0; p < n; p++, j += 4) {
      var R0 = (outF[0][p] - blk) * sc, G0 = (outF[1][p] - blk) * sc, B0 = (outF[2][p] - blk) * sc;
      var Y = 0.299 * R0 + 0.587 * G0 + 0.114 * B0;
      out[j] = 255 * (Y + (R0 - Y) * SAT);
      out[j + 1] = 255 * (Y + (G0 - Y) * SAT);
      out[j + 2] = 255 * (Y + (B0 - Y) * SAT);
      out[j + 3] = 255;
    }
    tick('done');
    return out;
  }

  var api = { fuse: fuse };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (typeof self !== 'undefined' && typeof window === 'undefined' && typeof importScripts === 'function') {
    self.onmessage = function (ev) {
      var d = ev.data;
      try {
        var res = fuse(d.imgs, d.w, d.h, function (f, label) { self.postMessage({ type: 'progress', f: f, label: label }); });
        self.postMessage({ type: 'done', data: res, w: d.w, h: d.h }, [res.buffer]);
      } catch (e) {
        self.postMessage({ type: 'error', message: String(e && e.message || e) });
      }
    };
  }
})();
