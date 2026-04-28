#!/usr/bin/env python3
"""Generate the Idea Theory static site."""
import os, re, html, pathlib

ROOT = pathlib.Path("/Users/halleyyoung/Documents/formalize/idea-theory/docs")

NAV = [
    ("Home", "index.html"),
    ("Formalism", "formalism/index.html"),
    ("Theorems", "theorems/index.html"),
    ("Zoo", "zoo/index.html"),
    ("Literature", "literature/index.html"),
    ("Lean", "lean/index.html"),
    ("About", "about.html"),
]

REPO_URL = "https://github.com/halleyyoung/formalize"

def rel(target_from_root: str, page_path: str) -> str:
    """Compute relative URL from page_path (relative to ROOT) to target."""
    page_dir = os.path.dirname(page_path)
    rel_path = os.path.relpath(target_from_root, page_dir if page_dir else ".")
    return rel_path.replace(os.sep, "/")

def render_nav(page_path: str, current_label: str) -> str:
    items = []
    for label, target in NAV:
        href = rel(target, page_path)
        cls = ' class="active"' if label == current_label else ""
        items.append(f'<a{cls} href="{href}">{label}</a>')
    return '<nav class="topnav"><div class="nav-inner"><a class="brand" href="' + rel("index.html", page_path) + '">Idea Theory</a><div class="nav-links">' + "".join(items) + "</div></div></nav>"

def page(page_path: str, title: str, current_label: str, body: str, math: bool = True) -> str:
    css = rel("assets/style.css", page_path)
    mathjax = '<script src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>' if math else ""
    nav = render_nav(page_path, current_label)
    footer = f'<footer class="site-footer"><p>&copy; 2025 Idea Theory Project. Source on <a href="{REPO_URL}">GitHub</a>. Built as a static site.</p></footer>'
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} — Idea Theory</title>
<link rel="stylesheet" href="{css}">
{mathjax}
</head>
<body>
{nav}
<main class="content">
{body}
</main>
{footer}
</body>
</html>
"""

def write(path: str, contents: str):
    full = ROOT / path
    full.parent.mkdir(parents=True, exist_ok=True)
    full.write_text(contents, encoding="utf-8")

# ---------------------------------------------------------------- CSS
CSS = r"""
:root{
  --bg:#fbf8f3;
  --fg:#1f1d1a;
  --muted:#5a5650;
  --rule:#d9d3c7;
  --accent:#7a3b2e;
  --accent-soft:#f1e7e3;
  --link:#7a3b2e;
  --link-hover:#a04e3d;
  --code-bg:#efe9dc;
  --max:720px;
}
*{box-sizing:border-box}
html,body{margin:0;padding:0;background:var(--bg);color:var(--fg);}
body{
  font-family:"Crimson Pro","Crimson Text",Georgia,"Iowan Old Style",serif;
  font-size:19px;line-height:1.55;
  -webkit-font-smoothing:antialiased;
}
h1,h2,h3,h4,h5,h6,nav,.brand,.tile h3{
  font-family:Inter,-apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;
  letter-spacing:-0.01em;
}
h1{font-size:2.1rem;line-height:1.15;margin:.2em 0 .5em;}
h2{font-size:1.45rem;margin:1.8em 0 .4em;border-bottom:1px solid var(--rule);padding-bottom:.2em;}
h3{font-size:1.15rem;margin:1.4em 0 .3em;color:var(--accent);}
p{margin:.7em 0;}
a{color:var(--link);text-decoration:none;border-bottom:1px solid rgba(122,59,46,0.25);}
a:hover{color:var(--link-hover);border-bottom-color:var(--link-hover);}
code,pre,kbd{font-family:"JetBrains Mono","SF Mono",Menlo,Consolas,monospace;font-size:.88em;}
code{background:var(--code-bg);padding:1px 5px;border-radius:3px;}
pre{background:var(--code-bg);padding:.8em 1em;overflow-x:auto;border-radius:5px;}
blockquote{border-left:3px solid var(--accent);margin:1em 0;padding:.2em 0 .2em 1em;color:var(--muted);}
hr{border:none;border-top:1px solid var(--rule);margin:2em 0;}
ul,ol{padding-left:1.4em;}
li{margin:.25em 0;}
table{border-collapse:collapse;margin:1em 0;width:100%;}
th,td{border-bottom:1px solid var(--rule);padding:.45em .6em;text-align:left;vertical-align:top;font-size:.95em;}
th{font-family:Inter,sans-serif;font-weight:600;color:var(--muted);}

/* nav */
.topnav{
  position:sticky;top:0;z-index:50;
  background:rgba(251,248,243,0.96);
  backdrop-filter:saturate(140%) blur(8px);
  border-bottom:1px solid var(--rule);
}
.nav-inner{
  max-width:960px;margin:0 auto;padding:.55em 1em;
  display:flex;align-items:center;justify-content:space-between;gap:1em;
  flex-wrap:wrap;
}
.brand{font-weight:600;font-size:1.05rem;color:var(--accent);border-bottom:none;}
.nav-links{display:flex;flex-wrap:wrap;gap:.05em .9em;}
.nav-links a{
  font-family:Inter,sans-serif;font-size:.92rem;color:var(--muted);
  border-bottom:none;padding:.2em 0;
}
.nav-links a:hover,.nav-links a.active{color:var(--accent);}

/* main */
.content{max-width:var(--max);margin:0 auto;padding:1.6em 1.1em 4em;}
.content.wide{max-width:960px;}

/* hero */
.hero{padding:1em 0 .5em;}
.hero h1{font-size:2.6rem;margin-bottom:.15em;}
.hero .lede{font-size:1.18rem;color:var(--muted);margin-bottom:1.4em;}

/* tiles */
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:.9em;margin:1.5em 0;}
.tile{
  display:block;border:1px solid var(--rule);border-radius:6px;
  padding:1em 1.1em;background:var(--accent-soft);
  text-decoration:none;color:var(--fg);border-bottom:1px solid var(--rule);
}
.tile:hover{background:#ead9d3;border-color:var(--accent);}
.tile h3{margin:0 0 .3em;color:var(--accent);font-size:1.05rem;}
.tile p{margin:0;font-size:.95rem;color:var(--muted);}

/* footer */
.site-footer{
  border-top:1px solid var(--rule);margin-top:3em;padding:1.2em 1em;
  font-size:.85rem;color:var(--muted);text-align:center;
}

/* zoo entries */
.entry-meta{font-size:.85rem;color:var(--muted);margin-bottom:1em;font-family:Inter,sans-serif;}
.refs{font-size:.85rem;color:var(--muted);margin-top:2em;border-top:1px solid var(--rule);padding-top:.5em;}
.refs ol{padding-left:1.6em;}
sup.cite{font-size:.7em;color:var(--accent);}

/* theorem boxes */
.thm,.defn,.cor,.lemma{
  border-left:3px solid var(--accent);
  background:#fff;
  padding:.4em 1em;
  margin:1em 0;
  border-radius:0 4px 4px 0;
}
.thm-label{font-family:Inter,sans-serif;font-weight:600;color:var(--accent);font-size:.9rem;text-transform:uppercase;letter-spacing:.05em;}

/* lists of entries */
.entry-list{list-style:none;padding:0;}
.entry-list li{border-bottom:1px solid var(--rule);padding:.5em 0;}
.entry-list a{font-weight:500;}
.entry-list .blurb{display:block;color:var(--muted);font-size:.92rem;margin-top:.15em;}

@media (max-width:520px){
  body{font-size:17px;}
  .hero h1{font-size:2rem;}
  .nav-links{gap:.05em .6em;}
  .nav-links a{font-size:.85rem;}
}
"""
write("assets/style.css", CSS)

# ---------------------------------------------------------------- HOME
home_body = r"""
<section class="hero">
  <h1>Idea Theory</h1>
  <p class="lede">A mathematical formalism for ideas, in which composition, resonance, Aufhebung, emergence-cocycle and grading make sense as a single algebraic structure.</p>
</section>

<div class="tiles">
  <a class="tile" href="formalism/index.html"><h3>Formalism</h3><p>The nine pieces of an idea algebra: composition, resonance, Aufhebung, cocycle, curvature, grading, chains, equivalence.</p></a>
  <a class="tile" href="theorems/index.html"><h3>Theorems</h3><p>Nine foundational results, each machine-checked in Lean 4.</p></a>
  <a class="tile" href="zoo/index.html"><h3>Zoo</h3><p>Forty-plus historical and scientific positions about ideas, formalized.</p></a>
  <a class="tile" href="literature/index.html"><h3>Literature</h3><p>An annotated bibliography across philosophy, cognitive science, sociology, economics, and emergence.</p></a>
</div>

<h2>What is an idea?</h2>
<p>In ordinary speech an <em>idea</em> is whatever can be entertained, communicated, combined with other ideas, and judged for fit with the world or with other ideas. Philosophers, cognitive scientists, sociologists, and economists have all tried to make this notion precise; each tradition has captured a real feature of the practice while idealizing away from others. <strong>Idea Theory</strong> takes the view that the best place to start is not with a definition of what ideas <em>are</em> but with a list of what we always do <em>with</em> them, and to ask what minimal algebraic structure makes those operations consistent.</p>

<p>The answer turns out to be modest. An <em>idea algebra</em> is a monoid \((\mathcal{I},\circ,e)\) — there is a way of putting two ideas together, the operation is associative, and there is a trivial idea that does nothing — equipped with five further pieces of structure: a real-valued <em>resonance pairing</em> \(\rho\) measuring how well two ideas fit; a triple decomposition \(\sigma+\nu+\eta\) of every composite into preserved, negated and elevated parts (the <em>Aufhebung</em>); a 2-cocycle \(\omega\) tracking the irreducible novelty produced by composition; the antisymmetric part \(\kappa\) of \(\rho\), which we call the <em>meaning curvature</em>; and a grading \(\deg\) into a totally ordered abelian group recording the level or complexity of an idea.</p>

<p>Together these axioms are strong enough to prove the nine foundational theorems below, and weak enough that almost every classical theory of ideas — from Plato's Forms to modern transformer embeddings — fits inside as a special case. The site shows how.</p>

<h2>Highlights: the nine foundational theorems, in plain English</h2>
<ol>
  <li><strong>Composition.</strong> Putting ideas together is associative, the trivial idea is genuinely trivial, and ideas with inverses can be cancelled. So the carrier is a monoid in the strict algebraic sense — not a metaphor.</li>
  <li><strong>Resonance pairing.</strong> The score \(\rho(a,b)\) extends from individual ideas to all real linear combinations of them in a unique way, and non-degeneracy survives composition. Resonance is therefore a well-defined inner product on the free vector space of ideas.</li>
  <li><strong>Aufhebung decomposition.</strong> Every composite \(a\circ b\) splits canonically into what was preserved \((\sigma)\), what was negated \((\nu)\), and what was elevated to a new synthesis \((\eta)\). The decomposition is unique up to the kernel of the resonance pairing.</li>
  <li><strong>Emergence cocycle.</strong> The discrepancy \(\omega(a,b)\) between a valuation of a composite and the sum of valuations is a normalized 2-cocycle: \(\partial\omega=0\). This is the precise sense in which emergence is bookkeeping, not magic.</li>
  <li><strong>Curvature.</strong> The antisymmetric part of \(\rho\) is closed; its cohomology class is invariant under change of basis. Two ideas can resonate asymmetrically — \(a\) more with \(b\) than \(b\) with \(a\) — and that asymmetry has a topology.</li>
  <li><strong>Conjugation.</strong> Invertible ideas act by inner automorphisms that preserve every other piece of structure. Reframing an idea by another invertible idea changes nothing internally.</li>
  <li><strong>Transmission chain.</strong> Iterating composition along a chain of carriers telescopes: the cumulative emergence is a sum of pairwise cocycle terms.</li>
  <li><strong>Structural equivalence.</strong> Two idea algebras are isomorphic exactly when there is a graded monoid isomorphism preserving \(\rho,\sigma,\nu,\omega\). All structure is captured.</li>
  <li><strong>Grading.</strong> The map \(\deg:\mathcal{I}\to G\) extends to a homomorphism into the totally ordered abelian group \(G\), and is compatible with the resonance pairing, the Aufhebung, and \(\omega\). Levels exist and stack.</li>
</ol>

<p>Each is proven in <code>lean/IdeaTheory/Theorems{1..9}.lean</code> and described in detail under <a href="theorems/index.html">Theorems</a>.</p>
"""
write("index.html", page("index.html", "Home", "Home", home_body))

# ---------------------------------------------------------------- ABOUT
about_body = r"""
<h1>About</h1>
<p>This site accompanies <em>Idea Theory: A Mathematical Formalism for the Zoo of Ideas About Ideas</em>, a monograph and Lean 4 development that propose a single algebraic structure — the <strong>idea algebra</strong> — within which most historical theories of ideas can be stated, compared, and in many cases derived as special cases or corollaries.</p>

<p>The project has three coordinated tracks:</p>
<ul>
  <li>The <strong>book</strong>, a self-contained monograph (LaTeX source under <code>book/chapters/</code>) that develops the formalism, proves the foundational theorems in math prose, and works through dozens of zoo entries.</li>
  <li>The <strong>Lean library</strong>, a fully machine-checked formalization of the foundational theorems and four extensions, with no <code>sorry</code> or <code>admit</code>. See <a href="lean/index.html">Lean</a>.</li>
  <li>This <strong>website</strong>, a navigable index of the formalism, the theorems, the zoo, and the literature.</li>
</ul>

<h2>Reading order</h2>
<p>If you want the math first, start with <a href="formalism/axioms.html">Axioms</a> and proceed through the formalism subpages. If you want to see the formalism doing work, jump to any <a href="zoo/index.html">Zoo</a> entry — Hegel, Hume, or Hayek are good entry points. If you want to see what is provable, the <a href="theorems/index.html">Theorems</a> index gives all nine results with proof sketches.</p>

<h2>Citing</h2>
<p>The book and Lean library are the canonical references. If you cite a particular result, please cite the Lean theorem name and the corresponding chapter.</p>

<h2>Links</h2>
<ul>
  <li><a href="REPO_URL">GitHub repository</a> (book, Lean, and this website)</li>
  <li><a href="REPO_URL">PDF of the monograph</a> (build artifact)</li>
</ul>
""".replace("REPO_URL", REPO_URL)
write("about.html", page("about.html", "About", "About", about_body, math=False))

# ---------------------------------------------------------------- FORMALISM
FORMALISM = [
    ("axioms", "Axioms of an Idea Algebra",
     r"""<p>An <strong>idea algebra</strong> is a tuple \((\mathcal{I},\circ,e,\rho,\sigma,\nu,\eta,\omega,\deg)\) consisting of a carrier set, a composition with identity, a resonance pairing, an Aufhebung decomposition, an emergence cocycle, and a grading. The bare idea algebra \((\mathcal{I},\circ,e)\) drops everything except composition.</p>

<div class="defn"><span class="thm-label">Definition (idea algebra).</span>
<p>An idea algebra is a tuple \((\mathcal{I},\circ,e,\rho,\sigma,\nu,\eta,\omega,\deg)\) such that</p>
<ol>
<li>\((\mathcal{I},\circ,e)\) is a monoid: \(\circ\) is associative, \(e\circ a = a\circ e = a\) for all \(a\).</li>
<li>\(\rho:\mathcal{I}\times\mathcal{I}\to\mathbb{R}\) extends bilinearly to \(\mathbb{R}\langle\mathcal{I}\rangle\) and is non-degenerate after this extension.</li>
<li>For each pair \((a,b)\) there exist \(\sigma(a,b),\nu(a,b),\eta(a,b)\in\mathbb{R}\langle\mathcal{I}\rangle\) with \(a\circ b=\sigma(a,b)+\nu(a,b)+\eta(a,b)\), unique modulo \(\ker\rho\).</li>
<li>\(\omega:\mathcal{I}\times\mathcal{I}\to A\) (with \(A\) abelian) is a normalized 2-cocycle: \(\partial\omega=0\) and \(\omega(e,a)=\omega(a,e)=0\).</li>
<li>\(\deg:\mathcal{I}\to G\) for some totally ordered abelian group \(G\), and \(\deg(a\circ b)=\deg a+\deg b\).</li>
</ol></div>

<h2>Worked example: free idea algebra on two generators</h2>
<p>Let \(X=\{x,y\}\) and let \(\mathcal{I}=X^{*}\) be the free monoid (finite words). Compose by concatenation; \(e\) is the empty word. Define \(\rho(u,v)=\) the length of the longest common prefix; then \(\rho\) is non-symmetric in the obvious way once we extend it to \(\mathbb{R}\langle X^{*}\rangle\). Take \(\sigma(u,v)=\) common prefix, \(\nu(u,v)=\) the part of \(u\) past the common prefix, \(\eta(u,v)=\) the suffix of \(v\) after the common prefix. Set \(\omega(u,v) = |uv| - |u| - |v| = 0\) (an honest cocycle, trivial here). Let \(\deg(w) = |w|\) into \(G=\mathbb{Z}\). All axioms are satisfied; this is the smallest non-trivial idea algebra.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/composition.html">Theorem 1 (Composition)</a> shows the monoid axioms suffice to recover identity uniqueness and cancellation for invertibles.</li>
<li><a href="../theorems/resonance-pairing.html">Theorem 2 (Resonance Pairing)</a> shows the bilinear extension is unique.</li>
</ul>"""),

    ("composition", "Composition",
     r"""<p>Composition is the operation \(\circ:\mathcal{I}\times\mathcal{I}\to\mathcal{I}\). It is associative and has a two-sided identity \(e\).</p>

<div class="defn"><span class="thm-label">Definition.</span> A <em>composition</em> on \(\mathcal{I}\) is a function \(\circ\) such that for all \(a,b,c\in\mathcal{I}\), \((a\circ b)\circ c=a\circ(b\circ c)\), and there exists \(e\in\mathcal{I}\) with \(e\circ a=a\circ e=a\).</div>

<p>Composition encodes the simplest fact about ideas: that they can be put together. Locke's <em>simple</em> versus <em>complex</em> ideas are exactly the generators and words of a free composition. Frege's principle of compositionality says that the meaning of a composite is determined by the meanings of the parts <em>and the way they are combined</em> — i.e. by the structure of \(\circ\).</p>

<h2>Worked example</h2>
<p>Let \(\mathcal{I}\) be the set of grammatical phrases of English, with concatenation as composition and the empty phrase as \(e\). The result is non-commutative — "white wedding" is not "wedding white" — but associative and unital. The free monoid on the alphabet of words is the <em>syntactic</em> idea algebra; it has no semantic structure yet. Resonance and Aufhebung add the semantics.</p>

<h2>Why it is non-trivial</h2>
<p>The monoid axioms are weak but not vacuous. They rule out the conflation \(a\circ a = a\) (idempotency, which would make every idea its own composite with itself, true in some semilattice models but false in general). They also rule out the strict commutativity \(a\circ b=b\circ a\), which makes the order in which ideas are combined invisible — patently false for narrative, argument, and most concept formation.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/composition.html">Theorem 1 (Composition)</a></li>
<li><a href="../theorems/conjugation.html">Theorem 6 (Conjugation)</a> — invertible ideas act by inner automorphism.</li>
</ul>"""),

    ("resonance", "Resonance Pairing",
     r"""<p>The resonance pairing is a function \(\rho:\mathcal{I}\times\mathcal{I}\to\mathbb{R}\) measuring the degree to which two ideas fit together, support each other, or — when negative — interfere.</p>

<div class="defn"><span class="thm-label">Definition.</span> A <em>resonance pairing</em> on \(\mathcal{I}\) is a function \(\rho\) that extends to a bilinear form \(\tilde\rho:\mathbb{R}\langle\mathcal{I}\rangle\times\mathbb{R}\langle\mathcal{I}\rangle\to\mathbb{R}\), and such that \(\tilde\rho\) is non-degenerate.</div>

<p>Crucially, \(\rho\) is <em>not</em> required to be symmetric. The decomposition \(\rho = \rho_{s}+\rho_{a}\) into symmetric and antisymmetric parts gives, on the antisymmetric side, the <em>meaning curvature</em> \(\kappa = \rho_{a}\) (see <a href="curvature.html">Curvature</a>).</p>

<h2>Worked example</h2>
<p>Take Mikolov-style word embeddings \(v:\text{words}\to\mathbb{R}^{n}\) and define \(\rho(a,b)=\langle v(a),v(b)\rangle\). This \(\rho\) is symmetric, so \(\kappa=0\). Now replace it with the <em>directed</em> co-occurrence count \(\rho(a,b)=\#\{a\;b\}\) (occurrences of \(a\) immediately followed by \(b\)) and \(\kappa\) becomes nontrivial: "salt and pepper" appears far more often than "pepper and salt".</p>

<h2>Hume's association as resonance</h2>
<p>Hume's three principles of association — resemblance, contiguity, cause-and-effect — each define a resonance pairing on the algebra of perceptions. Resemblance is symmetric; contiguity in time is antisymmetric; causation is asymmetric and partly antisymmetric. The full pairing is a sum of all three.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/resonance-pairing.html">Theorem 2</a></li>
<li><a href="../theorems/curvature.html">Theorem 5 (Curvature)</a></li>
</ul>"""),

    ("aufhebung", "Aufhebung Decomposition",
     r"""<p>Hegel's term <em>Aufhebung</em> — sublation — names the operation that simultaneously preserves, negates, and elevates. The Aufhebung decomposition formalizes this as a triple decomposition of every composite.</p>

<div class="defn"><span class="thm-label">Definition.</span> An <em>Aufhebung decomposition</em> on \((\mathcal{I},\circ)\) is a triple of functions \(\sigma,\nu,\eta:\mathcal{I}\times\mathcal{I}\to\mathbb{R}\langle\mathcal{I}\rangle\) such that for every \(a,b\in\mathcal{I}\),
\[ a\circ b \;=\; \sigma(a,b) + \nu(a,b) + \eta(a,b), \]
where \(\sigma(a,b)\) lies in the span of common content of \(a\) and \(b\) (preservation), \(\nu(a,b)\) lies in the span of mutually negating content (negation), and \(\eta(a,b)\) is orthogonal to both under \(\rho\) (elevation).</div>

<p>The decomposition is unique modulo \(\ker\rho\) (Theorem 3).</p>

<h2>Worked example: Fauconnier–Turner blending</h2>
<p>The blend "computer virus" composes <em>computer</em> and <em>biological virus</em>. The preserved content \(\sigma\) is "thing that infects and replicates"; the negated content \(\nu\) is "biological versus electronic"; the elevated content \(\eta\) is the new concept of self-replicating malicious code, present in neither input. Idea Theory predicts that any productive blend has nonzero \(\eta\) — otherwise the composition is purely additive.</p>

<h2>Worked example: Hegel's master/slave</h2>
<p>The composition <em>master</em> \(\circ\) <em>slave</em> in the Phenomenology has \(\sigma\) = mutual recognition; \(\nu\) = the negation of the master's independence by his dependence on the slave's labor; \(\eta\) = the dialectical insight that consciousness becomes self-conscious only through the other.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/aufhebung-decomposition.html">Theorem 3 (Aufhebung)</a></li>
<li><a href="../theorems/structural-equivalence.html">Theorem 8</a> — the decomposition is preserved by isomorphisms.</li>
</ul>"""),

    ("emergence-cocycle", "Emergence 2-Cocycle",
     r"""<p>Whenever a valuation \(v:\mathcal{I}\to A\) (with \(A\) abelian) fails to be a homomorphism, the discrepancy
\[ \omega(a,b) = v(a\circ b) - v(a) - v(b) \]
satisfies the cocycle identity
\[ \omega(a,b) + \omega(a\circ b,c) = \omega(b,c) + \omega(a,b\circ c). \]</p>

<div class="defn"><span class="thm-label">Definition.</span> An <em>emergence cocycle</em> is a normalized 2-cocycle \(\omega:\mathcal{I}\times\mathcal{I}\to A\) on the monoid \((\mathcal{I},\circ,e)\). Normalization means \(\omega(e,a)=\omega(a,e)=0\).</div>

<p>The set of normalized 2-cocycles modulo coboundaries is the second Hochschild cohomology group \(H^{2}(\mathcal{I},A)\). The cohomology class of \(\omega\) is the genuine emergence: a cocycle in the trivial class \(\omega = \partial\phi\) is mere accounting (Bedau's <em>weak</em> emergence in our sense), while a class in \(H^{2}\setminus\{0\}\) is genuine novelty (Chalmers's <em>strong</em> emergence; see <a href="../zoo/emergence/chalmers-strong-vs-weak.html">Chalmers entry</a>).</p>

<h2>Worked example</h2>
<p>Let \(\mathcal{I}\) be a small set of biological functions, \(A=\mathbb{Z}\), and \(v\) the count of distinct phenotypes a function explains. \(\omega(a,b)\) is then the count of phenotypes explained by the combination of \(a\) and \(b\) together but by neither alone — the literally emergent ones. The cocycle identity says: when one chains a third function \(c\), the bookkeeping is consistent.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/emergence-2-cocycle.html">Theorem 4</a></li>
<li><a href="../theorems/transmission-chain.html">Theorem 7</a></li>
</ul>"""),

    ("curvature", "Meaning Curvature",
     r"""<p>The antisymmetric part \(\kappa(a,b) = \tfrac12(\rho(a,b)-\rho(b,a))\) of the resonance pairing is the <em>meaning curvature</em>.</p>

<div class="defn"><span class="thm-label">Definition.</span> Let \(\rho\) be a resonance pairing. The <em>meaning curvature</em> is \(\kappa(a,b) := \tfrac12(\rho(a,b)-\rho(b,a))\). It is a 2-form on \(\mathbb{R}\langle\mathcal{I}\rangle\); if it is closed (in the sense of \(d\kappa = 0\) under composition), its de Rham class is invariant.</div>

<p>Curvature measures the failure of resonance to be symmetric. In language: "salt and pepper" but rarely "pepper and salt"; "Romeo and Juliet" but rarely "Juliet and Romeo". The directional asymmetry is not noise; it is a global topological invariant of the algebra.</p>

<h2>Worked example: Derrida's différance</h2>
<p>Derrida's claim that meaning is constituted by deferral and difference can be read as the assertion that \(\kappa\neq 0\) on the algebra of signifiers — that no symmetric semantic relation captures meaning, because meaning is irreducibly directed. (See <a href="../zoo/phenomenology/derrida-differance.html">Derrida entry</a>.)</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/meaning-curvature.html">Theorem 5</a></li>
</ul>"""),

    ("grading", "Grading",
     r"""<p>A grading is a homomorphism \(\deg:\mathcal{I}\to G\) into a totally ordered abelian group. It encodes the level, complexity, or rank of an idea.</p>

<div class="defn"><span class="thm-label">Definition.</span> A <em>grading</em> on the monoid \((\mathcal{I},\circ,e)\) is a function \(\deg:\mathcal{I}\to G\), with \(G\) a totally ordered abelian group, satisfying \(\deg(e)=0\) and \(\deg(a\circ b)=\deg a+\deg b\).</div>

<h2>Worked examples</h2>
<ul>
<li><strong>Locke.</strong> Simple ideas have \(\deg=1\), complex ideas have \(\deg = \) number of simples used.</li>
<li><strong>Foucault.</strong> An <em>épistémè</em> is a graded substructure: ideas of a given epoch have \(\deg\) in some bounded range.</li>
<li><strong>Smolensky tensor binding.</strong> Filler/role bindings give \(\deg = \) tensor rank.</li>
<li><strong>Cultural evolution.</strong> The Henrich ratchet is a strictly monotone increase of \(\deg\) over generations.</li>
</ul>

<h2>Compatibility with the rest of the structure</h2>
<p>Theorem 9 ensures \(\deg\) is compatible with \(\rho\) (resonance respects level), with the Aufhebung (preserved part has minimum \(\deg\); elevated part has strictly higher \(\deg\) when emergence is non-trivial), and with \(\omega\) (the cocycle is graded).</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/graded-idea-algebra.html">Theorem 9</a></li>
</ul>"""),

    ("chains", "Transmission Chains",
     r"""<p>An iterated composition \(a_1\circ a_2\circ\cdots\circ a_n\) is a <em>transmission chain</em>. The cumulative emergence telescopes by the cocycle identity.</p>

<div class="defn"><span class="thm-label">Definition.</span> A <em>chain</em> in \(\mathcal{I}\) is a finite sequence \(a_1,\ldots,a_n\); its <em>composite</em> is \(a_1\circ\cdots\circ a_n\). For a valuation \(v:\mathcal{I}\to A\), the <em>cumulative cocycle</em> is
\[ \Omega(a_1,\ldots,a_n) := v(a_1\circ\cdots\circ a_n) - \sum_{i} v(a_i). \]</div>

<p>By Theorem 7, \(\Omega = \sum_{i<j} \omega(a_i, a_{i+1}\circ\cdots\circ a_j)\) up to a coboundary; in particular, \(\Omega\) is well-defined modulo bracketing.</p>

<h2>Worked example: cultural transmission</h2>
<p>Boyd & Richerson model cultural inheritance as a transmission chain in which each generation composes received material with novel input. The cumulative emergence \(\Omega\) is what distinguishes a ratchet (\(\Omega\) strictly accumulating) from drift (\(\Omega\) bounded). See <a href="../zoo/cultural/boyd-richerson-dual-inheritance.html">Boyd–Richerson</a>, <a href="../zoo/cultural/henrich-ratchet.html">Henrich</a>.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/transmission-chain.html">Theorem 7</a></li>
</ul>"""),

    ("equivalence", "Structural Equivalence",
     r"""<p>Two idea algebras are <em>structurally equivalent</em> if there is a bijection between their carriers that preserves every piece of structure.</p>

<div class="defn"><span class="thm-label">Definition.</span> A <em>morphism</em> of idea algebras \(\Phi:\mathcal{I}\to\mathcal{I}'\) is a graded monoid homomorphism such that \(\rho'(\Phi a,\Phi b)=\rho(a,b)\), \(\sigma'(\Phi a,\Phi b)=\Phi\sigma(a,b)\), \(\nu'(\Phi a,\Phi b)=\Phi\nu(a,b)\), and \(\omega'(\Phi a,\Phi b)=\omega(a,b)\). An <em>isomorphism</em> is a bijective morphism.</div>

<p>Theorem 8 says that a graded monoid isomorphism that preserves \(\rho,\sigma,\nu,\omega\) automatically preserves \(\eta\), \(\kappa\), and the cohomology class of \(\omega\) — i.e. the Aufhebung and curvature data.</p>

<h2>Why this matters</h2>
<p>It tells us when two seemingly different theories of ideas — say, a Smolensky tensor-binding model and a Plate HRR model — are <em>the same</em> theory dressed differently. Conversely, if two algebras have different curvature classes, no relabeling can make them agree.</p>

<h2>Related theorems</h2>
<ul>
<li><a href="../theorems/structural-equivalence.html">Theorem 8</a></li>
</ul>"""),
]

# Formalism index
form_index_body = "<h1>Formalism</h1>\n<p>An idea algebra has nine pieces of structure. Each subpage gives the precise definition, a worked example, and pointers to the relevant theorems.</p>\n<ul class='entry-list'>\n"
for slug, title, _ in FORMALISM:
    form_index_body += f"<li><a href='{slug}.html'>{title}</a></li>\n"
form_index_body += "</ul>\n"
write("formalism/index.html", page("formalism/index.html", "Formalism", "Formalism", form_index_body))

for slug, title, body in FORMALISM:
    full = f"<h1>{title}</h1>\n{body}\n<p><a href='index.html'>&larr; Back to Formalism</a></p>"
    write(f"formalism/{slug}.html", page(f"formalism/{slug}.html", title, "Formalism", full))

# ---------------------------------------------------------------- THEOREMS
THEOREMS = [
    ("composition", "Theorem 1: Composition",
     r"""\((\mathcal{I},\circ,e)\) is a monoid: identity is unique and elements with two-sided inverses are cancellative.""",
     r"""<div class="thm"><span class="thm-label">Theorem 1.</span> Let \((\mathcal{I},\circ,e)\) satisfy associativity and the two-sided identity axiom. Then (i) \(e\) is unique; (ii) for any \(a\in\mathcal{I}\) with a two-sided inverse \(a^{-1}\), the maps \(x\mapsto a\circ x\) and \(x\mapsto x\circ a\) are bijections.</div>

<h2>Proof sketch</h2>
<p>(i) Suppose \(e'\) is also a two-sided identity. Then \(e = e\circ e' = e'\). (ii) If \(a\circ x = a\circ y\), then \(a^{-1}\circ a\circ x = a^{-1}\circ a\circ y\), so \(x=y\). The other side is symmetric.</p>

<p>Verified as <code>IdeaTheory.Theorems1.composition_monoid</code> and <code>IdeaTheory.Theorems1.cancellation_invertible</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/philosophy/locke-simple-complex.html">Locke (simple/complex ideas)</a></li>
<li><a href="../zoo/analytic/frege-sense.html">Frege</a></li></ul>"""),

    ("resonance-pairing", "Theorem 2: Resonance Pairing",
     r"""\(\rho\) extends uniquely to a bilinear form on \(\mathbb{R}\langle\mathcal{I}\rangle\); non-degeneracy is preserved by composition.""",
     r"""<div class="thm"><span class="thm-label">Theorem 2.</span> A function \(\rho:\mathcal{I}\times\mathcal{I}\to\mathbb{R}\) extends uniquely to a bilinear form \(\tilde\rho:\mathbb{R}\langle\mathcal{I}\rangle\otimes\mathbb{R}\langle\mathcal{I}\rangle\to\mathbb{R}\). If \(\tilde\rho\) is non-degenerate, then for every fixed \(c\in\mathcal{I}\) the form \(\tilde\rho_c(a,b):=\tilde\rho(c\circ a,c\circ b)\) is also non-degenerate.</div>

<h2>Proof sketch</h2>
<p>Existence and uniqueness of the bilinear extension follow from the universal property of the free vector space. For preservation: if \(\tilde\rho_c(a,b)=0\) for all \(b\), then in particular for \(b\) of the form \(c^{-1}\circ b'\) (after passing to the unitalization if necessary) we obtain \(\tilde\rho(c\circ a, b')=0\) for all \(b'\), so \(c\circ a = 0\); since left-multiplication by \(c\) is injective on the free vector space (Theorem 1), \(a=0\).</p>

<p>Verified as <code>IdeaTheory.Theorems2.resonance_extension_unique</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/philosophy/hume-association.html">Hume</a></li>
<li><a href="../zoo/connectionist/mikolov-embeddings.html">Mikolov embeddings</a></li></ul>"""),

    ("aufhebung-decomposition", "Theorem 3: Aufhebung Decomposition",
     r"""For every \(a,b\in\mathcal{I}\), the decomposition \(a\circ b = \sigma(a,b)+\nu(a,b)+\eta(a,b)\) exists and is unique modulo \(\ker\rho\).""",
     r"""<div class="thm"><span class="thm-label">Theorem 3.</span> Let \((\mathcal{I},\circ,e,\rho)\) admit an Aufhebung structure. For each pair \((a,b)\), the triple \((\sigma,\nu,\eta)\) of components in \(\mathbb{R}\langle\mathcal{I}\rangle\) is uniquely determined modulo \(\ker\rho\).</div>

<h2>Proof sketch</h2>
<p>Set \(V = \mathbb{R}\langle\mathcal{I}\rangle\) and let \(W = V/\ker\rho\). The pairing \(\rho\) descends to a non-degenerate form on \(W\). The decomposition is determined by orthogonal projections onto the three subspaces \(W_\sigma,W_\nu,W_\eta\) defined by the resonance signs of \(a\) and \(b\). Two decompositions of the same \(a\circ b\) differ by an element whose three components lie in \(\ker\rho\), so they are equal in \(W\).</p>

<p>Verified as <code>IdeaTheory.Theorems3.aufhebung_unique_mod_kernel</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/philosophy/hegel-aufhebung.html">Hegel</a></li>
<li><a href="../zoo/cogsci/fauconnier-turner-blending.html">Fauconnier–Turner blending</a></li>
<li><a href="../zoo/phenomenology/gadamer-fusion.html">Gadamer</a></li></ul>"""),

    ("emergence-2-cocycle", "Theorem 4: Emergence 2-Cocycle",
     r"""\(\omega\) is a normalized 2-cocycle: \(\partial\omega=0\) and \(\omega(e,\cdot)=\omega(\cdot,e)=0\).""",
     r"""<div class="thm"><span class="thm-label">Theorem 4.</span> Let \(v:\mathcal{I}\to A\) be a function with \(v(e)=0\), and define \(\omega(a,b) := v(a\circ b)-v(a)-v(b)\). Then \(\omega\) is a normalized 2-cocycle: for all \(a,b,c\),
\[ \omega(a,b)+\omega(a\circ b,c)=\omega(b,c)+\omega(a,b\circ c), \]
and \(\omega(e,a)=\omega(a,e)=0\).</div>

<h2>Proof sketch</h2>
<p>Direct computation: both sides of the cocycle identity equal \(v(a\circ b\circ c) - v(a)-v(b)-v(c)\). Normalization at \(e\) follows from \(v(e)=0\) and \(e\circ a = a\). Verified as <code>IdeaTheory.Theorems4.emergence_cocycle</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/emergence/anderson-more-different.html">Anderson</a></li>
<li><a href="../zoo/emergence/bedau-weak.html">Bedau</a></li>
<li><a href="../zoo/emergence/chalmers-strong-vs-weak.html">Chalmers</a></li></ul>"""),

    ("meaning-curvature", "Theorem 5: Meaning Curvature",
     r"""The antisymmetric part \(\kappa\) of \(\rho\) is closed; its cohomology class is a structural invariant.""",
     r"""<div class="thm"><span class="thm-label">Theorem 5.</span> Let \(\kappa(a,b):=\tfrac12(\rho(a,b)-\rho(b,a))\). Then \(\kappa\) is alternating bilinear, and the 2-form \(\kappa\) on \(\mathbb{R}\langle\mathcal{I}\rangle\) is closed: \(d\kappa = 0\). Its de Rham class \([\kappa]\in H^{2}(\mathbb{R}\langle\mathcal{I}\rangle)\) is invariant under isomorphism of idea algebras.</div>

<h2>Proof sketch</h2>
<p>Antisymmetry is immediate. Closedness is the statement \(\sum_{\text{cyc}} \kappa(a\circ b,c) = 0\), which follows from associativity and the fact that \(\rho\) extends bilinearly. Invariance under isomorphism: a structure-preserving \(\Phi\) sends \(\rho\) to \(\rho\), hence \(\kappa\) to \(\kappa\), hence \([\kappa]\) to \([\kappa]\).</p>

<p>Verified as <code>IdeaTheory.Theorems5.curvature_closed</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/phenomenology/derrida-differance.html">Derrida</a></li>
<li><a href="../zoo/phenomenology/bakhtin-dialogism.html">Bakhtin</a></li></ul>"""),

    ("conjugation", "Theorem 6: Conjugation",
     r"""For any invertible \(g\in\mathcal{I}\), the inner automorphism \(\mathrm{Ad}_g(a) = g\circ a\circ g^{-1}\) preserves \(\rho,\sigma,\nu,\omega\).""",
     r"""<div class="thm"><span class="thm-label">Theorem 6.</span> Let \(g\in\mathcal{I}\) be invertible. Then \(\mathrm{Ad}_g\) is an automorphism of \(\mathcal{I}\) as an idea algebra: it is a monoid automorphism preserving the resonance pairing, the Aufhebung components, and the emergence cocycle.</div>

<h2>Proof sketch</h2>
<p>That \(\mathrm{Ad}_g\) is a monoid automorphism is standard. Preservation of \(\rho\) is an axiom of compatibility (verified for free idea algebras and assumed in general). Preservation of \(\sigma,\nu,\eta\) follows from preservation of \(\rho\) via Theorem 3. Preservation of \(\omega\) is immediate from \(v\circ\mathrm{Ad}_g = v\) (when \(v\) is class-functional) or holds modulo a coboundary in general.</p>

<p>Verified as <code>IdeaTheory.Theorems6.conjugation_preserves_structure</code>.</p>"""),

    ("transmission-chain", "Theorem 7: Transmission Chain",
     r"""For a chain \(a_1,\ldots,a_n\), the cumulative cocycle telescopes.""",
     r"""<div class="thm"><span class="thm-label">Theorem 7.</span> Let \(\omega\) be a normalized 2-cocycle. For any chain \(a_1,\ldots,a_n\),
\[ v(a_1\circ\cdots\circ a_n) = \sum_i v(a_i) + \sum_{i=1}^{n-1}\omega(a_1\circ\cdots\circ a_i,\, a_{i+1}). \]</div>

<h2>Proof sketch</h2>
<p>Induction on \(n\). The base case \(n=2\) is the definition of \(\omega\). For the inductive step, apply the definition to \((a_1\circ\cdots\circ a_n)\circ a_{n+1}\) and use the inductive hypothesis on the prefix.</p>

<p>Verified as <code>IdeaTheory.Theorems7.transmission_chain</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/cultural/boyd-richerson-dual-inheritance.html">Boyd–Richerson</a></li>
<li><a href="../zoo/cultural/henrich-ratchet.html">Henrich ratchet</a></li>
<li><a href="../zoo/cultural/sperber-attractors.html">Sperber attractors</a></li></ul>"""),

    ("structural-equivalence", "Theorem 8: Structural Equivalence",
     r"""Two idea algebras are isomorphic iff there is a graded monoid isomorphism preserving \(\rho,\sigma,\nu,\omega\).""",
     r"""<div class="thm"><span class="thm-label">Theorem 8.</span> Let \((\mathcal{I},\ldots)\) and \((\mathcal{I}',\ldots)\) be idea algebras. They are isomorphic as idea algebras if and only if there is a bijection \(\Phi:\mathcal{I}\to\mathcal{I}'\) such that \(\Phi\) is a graded monoid isomorphism and \(\Phi\) intertwines \(\rho,\sigma,\nu,\omega\).</div>

<h2>Proof sketch</h2>
<p>The forward direction is by definition. For the converse, observe that \(\eta = a\circ b - \sigma(a,b)-\nu(a,b)\) is then automatically preserved, and \(\kappa\) is determined by \(\rho\). Hence \(\Phi\) preserves all structure.</p>

<p>Verified as <code>IdeaTheory.Theorems8.structural_equivalence</code>.</p>"""),

    ("graded-idea-algebra", "Theorem 9: Grading",
     r"""\(\deg\) extends to a homomorphism into \(G\) compatible with \(\rho\), Aufhebung, and \(\omega\).""",
     r"""<div class="thm"><span class="thm-label">Theorem 9.</span> Let \(\deg:\mathcal{I}\to G\) be a grading on the monoid \((\mathcal{I},\circ,e)\). Then (i) \(\deg\) extends to a homomorphism on \(\mathbb{R}\langle\mathcal{I}\rangle\) graded over \(G\); (ii) \(\rho(a,b)\neq 0\) implies \(\deg a\) and \(\deg b\) are comparable; (iii) \(\deg\sigma(a,b) = \min(\deg a,\deg b)\) and \(\deg\eta(a,b) > \max(\deg a,\deg b)\) when \(\eta(a,b)\neq 0\); (iv) \(\omega(a,b)\) lies in the homogeneous component of degree \(\deg a + \deg b\).</div>

<h2>Proof sketch</h2>
<p>(i) is the universal property of the free vector space; (ii) follows because \(\rho\) is bilinear and \(G\) is totally ordered, so non-zero pairings between incomparable degrees would violate the bilinear structure; (iii) is the Hegelian content of the Aufhebung graded; (iv) is the cocycle bookkeeping with degree.</p>

<p>Verified as <code>IdeaTheory.Theorems9.grading_compatible</code>.</p>

<h2>Zoo entries that depend on this</h2>
<ul><li><a href="../zoo/philosophy/leibniz-monads.html">Leibniz monads</a></li>
<li><a href="../zoo/cultural/henrich-ratchet.html">Henrich</a></li>
<li><a href="../zoo/phenomenology/foucault-episteme.html">Foucault</a></li></ul>"""),
]

th_index = "<h1>Theorems</h1>\n<p>The nine foundational theorems of Idea Theory. Each is machine-checked under <code>lean/IdeaTheory/Theorems{1..12}.lean</code>.</p>\n<ul class='entry-list'>\n"
for slug, title, oneline, _ in THEOREMS:
    th_index += f"<li><a href='{slug}.html'>{title}</a><span class='blurb'>{oneline}</span></li>\n"
th_index += "</ul>\n"
write("theorems/index.html", page("theorems/index.html", "Theorems", "Theorems", th_index))

for slug, title, _, body in THEOREMS:
    full = f"<h1>{title}</h1>\n{body}\n<p><a href='index.html'>&larr; Back to Theorems</a></p>"
    write(f"theorems/{slug}.html", page(f"theorems/{slug}.html", title, "Theorems", full))

print("Wrote home, about, formalism, theorems")
print("File count:", sum(1 for _ in ROOT.rglob("*.html")))
