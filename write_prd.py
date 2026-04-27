import json

IDEA = "Idea Theory"
SOURCE_DOC = "/Users/halleyyoung/Documents/formalize/IDT_Theory.pdf"

VOL_TITLES = [
    "Mathematical Foundations of Idea Theory",
    "Idea Theory and the Social Sciences",
    "Idea Theory and the Humanities",
    "Idea Theory, Cognitive Science, and Philosophy of Mind",
    "Emergence: A Formal Theory",
]

ABSTRACT = (
    "Idea Theory develops a rigorous algebraic framework treating ideas as composable "
    "structures equipped with identity, resonance, weight, asymmetry, and emergence. "
    "Volume 1 lays the pure mathematical foundations — a monoid axiomatisation with "
    "real-valued resonance and a cocycle-condition for emergent surplus — proved in "
    "nine Lean 4 theorem files. Volumes 2-5 interpret these foundations across four "
    "domains: the social sciences (power structures, collective belief, network "
    "dynamics); the humanities (narrative composition, cultural transmission, "
    "hermeneutic circles); cognitive science and philosophy of mind (mental-model "
    "identity, cognitive schemas, consciousness); and the phenomenon of emergence "
    "itself (supervenience, complexity, formal emergence theorems). Each application "
    "volume contributes new Lean theorems, website pages, and LaTeX chapters that "
    "bridge the formal system to its target domain."
)

def lean_desc(n, topic, vol, vol_title, extra_imports=""):
    imports = "IdeaTheory.Foundations"
    if extra_imports:
        imports += ", " + extra_imports
    return (
        f"Create lean/IdeaTheory/Theorems{n}.lean for '{topic}'. "
        f"This file belongs to Volume {vol} ({vol_title}). "
        f"SUBSTANTIAL Lean 4 file (target 600-1500 lines). "
        f"Import {imports} and any needed sibling Theorems files. "
        f"Namespace IdeaTheory. Zero sorry/admit/native_decide/#check. "
        f"REQUIRED ARTIFACTS: "
        f"(1) FILE-LEVEL DOCSTRING: multi-paragraph /-! ... -/ (250-500 words) explaining "
        f"what informal content this formalizes, authors/works drawn on, design decisions, "
        f"roadmap, and role in Volume {vol}. "
        f"(2) AUXILIARY DEFINITIONS: 8-15 def/structure/abbrev with docstrings. "
        f"(3) HELPER LEMMA LAYER: 40-120 named lemmas in labeled section blocks. "
        f"(4) THREE HEADLINE THEOREMS named theorem_{n}_1, theorem_{n}_2, theorem_{n}_3, "
        f"each with 120-300-word docstring and multi-step tactic proof. "
        f"(5) 4+ COROLLARIES named corollary_{n}_*. "
        f"(6) 6+ EXAMPLES. "
        f"(7) END-OF-FILE INDEX block. "
        f"WORKFLOW: incremental batches, compile with lake build after each. "
        f"Read source document at {SOURCE_DOC} for domain context. "
        f"VOLUME CONTEXT: align emphasis with Volume {vol}: {vol_title}."
    )

tasks = []

# Toolchain
tasks.append({
    "id": "toolchain",
    "type": "lean_toolchain",
    "title": "Lean toolchain and lakefile",
    "description": "Create lean-toolchain (Lean 4.15.0) and lean/lakefile.lean requiring Mathlib.",
    "output_files": ["lean-toolchain", "lean/lakefile.lean"],
    "deps": [],
    "passes": True,
    "attempts": 1,
    "reviewer_notes": "wrote: lean-toolchain, lean/lakefile.lean",
})

# Foundations
tasks.append({
    "id": "foundations",
    "type": "lean_foundations",
    "title": "Lean 4 foundations",
    "description": (
        "Create lean/IdeaTheory/Foundations.lean. "
        "Author the foundational definitions, axioms, and structures for Idea Theory: "
        "the IdeaTheoryStructure type class (associative binary op, two-sided ident), "
        "real-valued resonance axioms (rs), noncomputable emergence, weight, and their "
        "basic axioms. Place everything inside `namespace IdeaTheory`. Zero sorries. "
        f"Read source document at {SOURCE_DOC} and build upon its mathematical content."
    ),
    "output_files": ["lean/IdeaTheory/Foundations.lean"],
    "deps": ["toolchain"],
    "passes": True,
    "attempts": 1,
    "reviewer_notes": "wrote: ",
})

# Vol 1 Lean theorems (Theorems1-9, all passes=True)
vol1_specs = [
    (1, "algebraic composition structure",
     "Core monoid structure: uniqueness of void, iteration/power laws, homomorphisms. "
     "Headline theorems: Composition Structure Theorem (unique identity, cancellation); "
     "Iteration/Power Structure Theorem (additive index law, commuting powers); "
     "Homomorphism/Combination Theorem (structure-preserving maps)."),
    (2, "emergence and the cocycle condition",
     "Emergence as trilinear deviation from additivity. "
     "Headline theorems: Trilinear Deviation Theorem; "
     "Cocycle Condition (fundamental cocycle equation from associativity); "
     "Emergence Bound (Cauchy-Schwarz-like inequality)."),
    (3, "resonance, weight, and Aufhebung decomposition",
     "Self-resonance weight function. "
     "Headline theorems: Strict Monotonicity Criterion (positive self-emergence implies weight increase); "
     "Weight Growth Under Powers (monotone non-decreasing weight sequence); "
     "Aufhebung Decomposition (weight = constituent resonances + dialectical surplus)."),
    (4, "asymmetry of resonance and meaning curvature",
     "Directional structure of resonance. "
     "Headline theorems: Resonance Decomposition and Symmetrization; "
     "Asymmetry Propagation Through Composition (with emergence correction); "
     "Meaning Curvature and Non-Commutativity."),
    (5, "idea structures, chains, and conjugation",
     "Structural invariants, composition chains, decompositions, conjugation. "
     "Headline theorems: Coherence Theorem; Decomposition Theorem; "
     "Conjugation-Preservation Theorem."),
    (6, "universal composition and foundational symmetry",
     "Universal finite composition, emergence chains, structural equivalence. "
     "Headline theorems: Universal Composition Theorem; "
     "Emergence Chain Theorem; Foundational Symmetry Theorem."),
    (7, "compositional identity and transmission chains",
     "Trivial idea uniqueness, identity transmission, compositional fixed points. "
     "Headline theorems: Identity Uniqueness Theorem; "
     "Identity Transmission Theorem; Fixed Point Theorem."),
    (8, "advanced properties and multi-term reassociation",
     "Identity absorption, four-term reassociation invariance, IdentSandwich and IdentChain. "
     "Headline theorems: Generalized Identity Absorption; "
     "Associative Regrouping Invariance (four-term products); "
     "Two-Sided Identity Uniqueness."),
    (9, "idea structures and structural equivalence",
     "Composite carriers, IdeaPair, IdeaTriple, BalancedIdea4. "
     "Headline theorems: Closure Theorem for Idea Pairs; "
     "Canonical Form Theorem for Idea Triples; "
     "Structural Equivalence Theorem."),
]

for n, topic, desc_extra in vol1_specs:
    tid = f"theorems_{n}"
    tasks.append({
        "id": tid,
        "type": "lean_theorems",
        "title": f"Lean theorems (Vol 1): {topic}",
        "description": (
            f"File lean/IdeaTheory/Theorems{n}.lean. Volume 1: {VOL_TITLES[0]}. "
            f"{desc_extra} "
            f"Import IdeaTheory.Foundations and any needed prior Theorems files. "
            f"Namespace IdeaTheory. Zero sorry/admit. "
            f"Required: file docstring, 8-15 aux defs, 40-120 helper lemmas, "
            f"3 headline theorems theorem_{n}_1/2/3 with 120-300-word docstrings, "
            f"4+ corollaries corollary_{n}_*, 6+ examples, end-of-file index."
        ),
        "output_files": [f"lean/IdeaTheory/Theorems{n}.lean"],
        "deps": ["foundations"] if n == 1 else ["foundations", f"theorems_{n-1}"],
        "passes": True,
        "attempts": 1,
        "reviewer_notes": "wrote: ",
    })

# Vol 2 Lean
tasks.append({
    "id": "theorems_10",
    "type": "lean_theorems",
    "title": "Lean theorems (Vol 2): social power, collective belief, and network dynamics",
    "description": lean_desc(
        10,
        "social power structures and collective belief aggregation",
        2, VOL_TITLES[1],
        extra_imports="IdeaTheory.Theorems4",
    ),
    "output_files": ["lean/IdeaTheory/Theorems10.lean"],
    "deps": ["theorems_4"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Vol 3 Lean
tasks.append({
    "id": "theorems_11",
    "type": "lean_theorems",
    "title": "Lean theorems (Vol 3): narrative composition and cultural transmission",
    "description": lean_desc(
        11,
        "narrative composition, hermeneutic circles, and cultural transmission",
        3, VOL_TITLES[2],
        extra_imports="IdeaTheory.Theorems5, IdeaTheory.Theorems6",
    ),
    "output_files": ["lean/IdeaTheory/Theorems11.lean"],
    "deps": ["theorems_6"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Vol 4 Lean
tasks.append({
    "id": "theorems_12",
    "type": "lean_theorems",
    "title": "Lean theorems (Vol 4): cognitive identity, mental models, and consciousness",
    "description": lean_desc(
        12,
        "cognitive identity persistence, mental model composition, and the structure of consciousness",
        4, VOL_TITLES[3],
        extra_imports="IdeaTheory.Theorems7, IdeaTheory.Theorems8",
    ),
    "output_files": ["lean/IdeaTheory/Theorems12.lean"],
    "deps": ["theorems_8"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Vol 5 Lean
tasks.append({
    "id": "theorems_13",
    "type": "lean_theorems",
    "title": "Lean theorems (Vol 5): formal emergence, supervenience, and complexity",
    "description": lean_desc(
        13,
        "formal emergence, supervenience relations, and complexity in idea systems",
        5, VOL_TITLES[4],
        extra_imports="IdeaTheory.Theorems2, IdeaTheory.Theorems9",
    ),
    "output_files": ["lean/IdeaTheory/Theorems13.lean"],
    "deps": ["theorems_9"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Website CSS
tasks.append({
    "id": "website_css",
    "type": "website_css",
    "title": "Website CSS",
    "description": (
        "Create docs/style.css — dark GitHub-style sidebar layout with responsive design. "
        "Sidebar 280px, fixed topbar 56px, main content area, themed for a formal mathematics site. "
        "Support 5-volume section headings in sidebar navigation."
    ),
    "output_files": ["docs/style.css"],
    "deps": ["toolchain"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Website index + navigation pages
tasks.append({
    "id": "website_index",
    "type": "website_index",
    "title": "Website index and navigation pages",
    "description": (
        "Create docs/index.html (project home), docs/axioms.html (foundations overview), "
        "docs/theorems.html (full theorem index across all 5 volumes), "
        "docs/volumes.html (5-volume landing page with cards for each volume). "
        "Each page uses docs/style.css and the full sidebar linking all 5 volumes and concept pages. "
        f"Project: Idea Theory. 5 volumes: {', '.join(VOL_TITLES)}."
    ),
    "output_files": [
        "docs/index.html", "docs/axioms.html", "docs/theorems.html", "docs/volumes.html",
    ],
    "deps": ["website_css"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Website: 5 volume landing pages
vol_page_specs = [
    ("vol1", "vol1.html", VOL_TITLES[0],
     "Links to all 9 core theorem concept pages (algebraic-structure, cocycle-condition, "
     "resonance-weight, asymmetry, idea-structures, composition-symmetry, "
     "identity-transmission, advanced-properties, structural-equivalence). "
     "Describes the algebraic framework: monoid structure, resonance, weight, asymmetry, "
     "emergence, cocycle condition, idea structures, structural equivalence."),
    ("vol2", "vol2.html", VOL_TITLES[1],
     "Links to social-sciences concept pages (social-power, collective-belief). "
     "Explains how Theorems4 and Theorems10 formalise power differentials, "
     "collective belief aggregation, and network dynamics. "
     "References Bourdieu (1984), Coleman (1990), Granovetter (1973)."),
    ("vol3", "vol3.html", VOL_TITLES[2],
     "Links to humanities concept pages (narrative-composition, cultural-transmission). "
     "Explains how Theorems5, 6, and 11 formalise narrative composition, "
     "hermeneutic circles, and cultural transmission chains. "
     "References Gadamer (1960), Ricoeur (1984), Barthes (1977)."),
    ("vol4", "vol4.html", VOL_TITLES[3],
     "Links to cogSci/philosophy-of-mind concept pages (cognitive-identity, consciousness). "
     "Explains how Theorems7, 8, and 12 formalise cognitive identity persistence, "
     "mental model composition, and the structure of consciousness. "
     "References Fodor (1975), Metzinger (2003), Chalmers (1996)."),
    ("vol5", "vol5.html", VOL_TITLES[4],
     "Links to emergence concept pages (formal-emergence, complexity). "
     "Explains how Theorems2, 9, and 13 formalise emergence as trilinear deviation, "
     "supervenience, and complexity in idea systems. "
     "References Kim (1993), Holland (1998), Anderson (1972)."),
]

for vid, vhtml, vtitle, vdesc in vol_page_specs:
    tasks.append({
        "id": f"website_{vid}",
        "type": "website_volumes",
        "title": f"Website volume page: {vtitle}",
        "description": (
            f"Create docs/{vhtml} — volume landing page for '{vtitle}'. "
            f"{vdesc} "
            f"Use docs/style.css. Full sidebar with all volumes and concept pages. "
            f"Include volume abstract, list of theorems, and links to concept pages."
        ),
        "output_files": [f"docs/{vhtml}"],
        "deps": ["website_index"],
        "passes": False,
        "attempts": 0,
        "reviewer_notes": "",
    })

# Website concept pages
concept_pages = [
    # Vol 1
    ("algebraic-structure",  "Algebraic Composition Structure",              "vol1", 1, "theorems_1"),
    ("cocycle-condition",     "Emergence and the Cocycle Condition",          "vol1", 1, "theorems_2"),
    ("resonance-weight",      "Resonance, Weight, and Aufhebung",             "vol1", 1, "theorems_3"),
    ("asymmetry",             "Asymmetry of Resonance and Meaning Curvature", "vol1", 1, "theorems_4"),
    ("idea-structures",       "Idea Structures, Chains, and Conjugation",     "vol1", 1, "theorems_5"),
    ("composition-symmetry",  "Universal Composition and Foundational Symmetry","vol1",1, "theorems_6"),
    ("identity-transmission", "Compositional Identity and Transmission",      "vol1", 1, "theorems_7"),
    ("advanced-properties",   "Advanced Properties and Reassociation",        "vol1", 1, "theorems_8"),
    ("structural-equivalence","Structural Equivalence",                       "vol1", 1, "theorems_9"),
    # Vol 2
    ("social-power",          "Social Power and Asymmetric Influence",        "vol2", 2, "theorems_10"),
    ("collective-belief",     "Collective Belief and Network Dynamics",       "vol2", 2, "theorems_10"),
    # Vol 3
    ("narrative-composition", "Narrative Composition and Hermeneutics",       "vol3", 3, "theorems_11"),
    ("cultural-transmission", "Cultural Transmission Chains",                 "vol3", 3, "theorems_11"),
    # Vol 4
    ("cognitive-identity",    "Cognitive Identity and Mental Models",         "vol4", 4, "theorems_12"),
    ("consciousness",         "Consciousness and the Composition of Mind",    "vol4", 4, "theorems_12"),
    # Vol 5
    ("formal-emergence",      "Formal Emergence and Supervenience",           "vol5", 5, "theorems_13"),
    ("complexity",            "Complexity in Idea Systems",                   "vol5", 5, "theorems_13"),
]

for slug, label, vol_id, vol_n, dep_id in concept_pages:
    tasks.append({
        "id": f"website_concept_{slug}",
        "type": "website_concept",
        "title": f"Website page: {label}",
        "description": (
            f"Create docs/{slug}.html — concept page for '{label}', Volume {vol_n} "
            f"({VOL_TITLES[vol_n-1]}). "
            f"Use docs/style.css with full sidebar. "
            f"Present informal exposition, formal theorem statements, proof sketches, "
            f"cross-references to relevant Lean file, and connections to the volume's domain. "
            f"Include at least one theorem-box and one definition-box."
        ),
        "output_files": [f"docs/{slug}.html"],
        "deps": [f"website_{vol_id}", dep_id],
        "passes": False,
        "attempts": 0,
        "reviewer_notes": "",
    })

# Website literature bridge
tasks.append({
    "id": "website_literature",
    "type": "website_literature",
    "title": "Website: literature bridge index",
    "description": (
        "Create docs/literature.html — bridge page mapping informal literature claims "
        "to formal Lean counterparts across all 5 volumes. "
        "Cross-reference: IDT_Theory.pdf (primary); social sciences (Bourdieu, Coleman); "
        "humanities (Gadamer, Ricoeur); cogSci (Fodor, Metzinger); "
        "emergence (Kim, Holland). Use docs/style.css with full sidebar."
    ),
    "output_files": ["docs/literature.html"],
    "deps": ["website_concept_structural-equivalence", "website_concept_formal-emergence"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# TeX preamble and bib
tasks.append({
    "id": "tex_preamble",
    "type": "tex_preamble",
    "title": "TeX preamble",
    "description": (
        "Create tex/preamble.sty — LaTeX preamble for a 5-volume monograph. "
        "Include: amsmath, amsthm, amssymb, mathtools, hyperref, cleveref, "
        "biblatex (biber backend), tikz, tcolorbox. "
        "Define theorem environments (theorem, lemma, corollary, definition, example, remark). "
        "Define volume-specific colour accents for Vols 1-5."
    ),
    "output_files": ["tex/preamble.sty"],
    "deps": ["toolchain"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

tasks.append({
    "id": "tex_bib",
    "type": "tex_bibliography",
    "title": "BibTeX bibliography",
    "description": (
        "Create tex/references.bib — BibTeX bibliography covering all 5 volumes. "
        "Include: IDT primary sources (Young 2024/2025); algebraic foundations (Mac Lane 1971, "
        "Bourbaki 1970, Clifford-Preston 1961, Howie 1995); social sciences (Bourdieu 1984, "
        "Coleman 1990, Granovetter 1973, Burt 1992); humanities (Gadamer 1960, Ricoeur 1984, "
        "Barthes 1977, Assmann 1995); cogSci/philosophy (Fodor 1975, Metzinger 2003, "
        "Chalmers 1996, Clark 1997, Johnson-Laird 1983); emergence/complexity (Kim 1993, "
        "Holland 1998, Anderson 1972, Kauffman 1993). At least 40 entries."
    ),
    "output_files": ["tex/references.bib"],
    "deps": ["toolchain"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# TeX diagrams
diagrams = [
    ("tex_diagram_1", "Monoid and Resonance Diagram",
     "TikZ diagram illustrating the monoid structure, resonance function rs, and "
     "the emergence function as a trilinear map on three ideas."),
    ("tex_diagram_2", "Five-Volume Architecture Diagram",
     "TikZ diagram showing how the 5 volumes relate: Vol 1 foundations feeding into "
     "Vols 2-5 applications, with arrows indicating formal dependencies."),
    ("tex_diagram_3", "Emergence Hierarchy Diagram",
     "TikZ diagram showing the emergence hierarchy: base monoid -> resonance/weight -> "
     "asymmetry -> emergence -> complexity, with application domains annotated."),
]

for did, dtitle, ddesc in diagrams:
    tasks.append({
        "id": did,
        "type": "tex_diagram",
        "title": f"TikZ diagram: {dtitle}",
        "description": (
            f"Create tex/figures/{did}.tex. {ddesc} "
            f"Standalone TikZ figure compilable with pdflatex."
        ),
        "output_files": [f"tex/figures/{did}.tex"],
        "deps": ["tex_preamble"],
        "passes": False,
        "attempts": 0,
        "reviewer_notes": "",
    })

# TeX chapters and volume mains
vol_chapter_specs = [
    (1, [
        ("v1c1", "Mathematical Preliminaries and the IdeaTheory Axioms",
         "Covers IdeaTheoryStructure axioms, resonance, weight, and the cocycle condition. "
         "Formalizes content of Theorems1-3. Algebraic treatment only."),
        ("v1c2", "Asymmetry, Structures, and Structural Equivalence",
         "Covers asymmetry, idea structures, conjugation, universal composition, "
         "structural equivalence. Formalizes Theorems4-9."),
    ]),
    (2, [
        ("v2c1", "Power, Influence, and Social Asymmetry",
         "Interprets asymmetry of resonance as social power differentials and status hierarchies. "
         "Draws on Theorems4 and Theorems10. References Bourdieu (1984), Granovetter (1973)."),
        ("v2c2", "Collective Belief and Network Dynamics",
         "Models collective belief aggregation via idea composition and network propagation. "
         "Draws on Theorems10. References Coleman (1990), Burt (1992)."),
    ]),
    (3, [
        ("v3c1", "Narrative Composition and Hermeneutic Circles",
         "Formalises narrative as composition chains with conjugation as interpretive framing. "
         "Draws on Theorems5, 6, 11. References Gadamer (1960), Ricoeur (1984)."),
        ("v3c2", "Cultural Transmission and the Emergence of Tradition",
         "Models cultural transmission via emergence chains and the cocycle condition. "
         "Draws on Theorems11. References Barthes (1977), Assmann (1995)."),
    ]),
    (4, [
        ("v4c1", "Cognitive Identity and the Persistence of Mental Models",
         "Interprets identity-transmission theorems as persistence of cognitive schemas. "
         "Draws on Theorems7, 12. References Fodor (1975), Johnson-Laird (1983)."),
        ("v4c2", "Consciousness, Composition, and the Hard Problem",
         "Uses advanced properties and structural equivalence to model conscious state composition. "
         "Draws on Theorems8, 12. References Metzinger (2003), Chalmers (1996)."),
    ]),
    (5, [
        ("v5c1", "Formal Emergence and the Cocycle Condition",
         "Shows that the cocycle condition formalises standard criteria for genuine emergence. "
         "Draws on Theorems2, 13. References Kim (1993), Holland (1998)."),
        ("v5c2", "Supervenience, Complexity, and Open Problems",
         "Formalises supervenience via structural equivalence; discusses open formal questions. "
         "Draws on Theorems9, 13. References Kim (1993), Anderson (1972), Kauffman (1993)."),
    ]),
]

for vol_n, chapters in vol_chapter_specs:
    vtitle = VOL_TITLES[vol_n - 1]
    ch_ids = []
    for ch_id, ch_title, ch_desc in chapters:
        full_id = f"tex_chapter_{ch_id}"
        tasks.append({
            "id": full_id,
            "type": "tex_chapter",
            "title": f"TeX ch (V{vol_n}): {ch_title}",
            "description": (
                f"Create tex/vol{vol_n}/{ch_id}.tex — chapter '{ch_title}' "
                f"for Volume {vol_n}: {vtitle}. "
                f"{ch_desc} "
                f"Use \\input{{../preamble.sty}}. "
                f"Include theorem/definition/example environments. "
                f"Minimum 2000 words. All \\cite keys must resolve in tex/references.bib."
            ),
            "output_files": [f"tex/vol{vol_n}/{ch_id}.tex"],
            "deps": ["tex_preamble", "tex_bib"],
            "passes": False,
            "attempts": 0,
            "reviewer_notes": "",
        })
        ch_ids.append(full_id)

    tasks.append({
        "id": f"tex_vol{vol_n}_main",
        "type": "tex_volume_main",
        "title": f"TeX volume {vol_n} main",
        "description": (
            f"Create tex/vol{vol_n}/main.tex — main file for Volume {vol_n}: {vtitle}. "
            f"\\input all chapters in this volume. Include title page, TOC, bibliography. "
            f"Must compile with pdflatex -interaction=nonstopmode."
        ),
        "output_files": [f"tex/vol{vol_n}/main.tex"],
        "deps": ch_ids,
        "passes": False,
        "attempts": 0,
        "reviewer_notes": "",
    })

# TeX omnibus
tasks.append({
    "id": "tex_omnibus",
    "type": "tex_omnibus",
    "title": "TeX omnibus spine",
    "description": (
        "Create tex/omnibus.tex — omnibus file including all 5 volumes as a single document. "
        "Unified numbering. Title: 'Idea Theory: A Five-Volume Formal Treatment'. "
        "Must compile with pdflatex."
    ),
    "output_files": ["tex/omnibus.tex"],
    "deps": [f"tex_vol{v}_main" for v in range(1, 6)],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# GitHub Pages
tasks.append({
    "id": "github_pages",
    "type": "github_pages",
    "title": "GitHub Pages deployment",
    "description": (
        "Create docs/_config.yml (Jekyll config) and "
        ".github/workflows/pages.yml (deploy docs/ to GitHub Pages on push to main). "
        "Ensure docs/.nojekyll exists. Workflow must pass yamllint."
    ),
    "output_files": ["docs/_config.yml", ".github/workflows/pages.yml"],
    "deps": ["website_literature"],
    "passes": False,
    "attempts": 0,
    "reviewer_notes": "",
})

# Assemble PRD
prd = {
    "idea": IDEA,
    "project_name": "IdeaTheory",
    "namespace": "IdeaTheory",
    "slug": "idea-theory",
    "abstract": ABSTRACT,
    "tasks": tasks,
    "n_volumes": 5,
    "volume_titles": VOL_TITLES,
    "branch_name": "formalize",
    "source_doc_path": SOURCE_DOC,
}

# Validate: no duplicate IDs
ids = [t["id"] for t in tasks]
dupes = [i for i in ids if ids.count(i) > 1]
if dupes:
    print("DUPLICATE IDs:", set(dupes))
else:
    print(f"OK: {len(tasks)} tasks, no duplicates")
    done = sum(1 for t in tasks if t["passes"])
    print(f"  passes=True: {done}  passes=False: {len(tasks)-done}")
    print(f"  n_volumes: {prd['n_volumes']}")
    print(f"  volume_titles: {prd['volume_titles']}")

with open("PRD.json", "w") as f:
    json.dump(prd, f, indent=2)
print("Wrote PRD.json")
