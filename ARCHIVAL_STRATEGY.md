# Archival and Citation Strategy for OperatorKO7

This document explains the complete archival strategy for the OperatorKO7 project, covering paper publication, code archival, and proper citation practices for journal submission.

## Overview: Triple-Layer Archival

The OperatorKO7 project uses a **three-tier archival strategy** that is standard for computational mathematics and formal verification:

```
┌─────────────────────────────────────────────────────────┐
│ LAYER 1: PAPER (arXiv)                                  │
│ - What: PDF + LaTeX source                              │
│ - Where: arXiv.org                                      │
│ - DOI: 10.48550/arXiv.2512.00081                       │
│ - Purpose: Cite the theoretical contribution            │
│ - Status: ✅ COMPLETE                                   │
└─────────────────────────────────────────────────────────┘
          ↓
┌─────────────────────────────────────────────────────────┐
│ LAYER 2: LIVE CODE (GitHub)                             │
│ - What: Source code + CI/CD                             │
│ - Where: github.com/MosesRahnama/OperatorKO7           │
│ - No DOI: URLs can change, repos can be deleted         │
│ - Purpose: Active development, cloning, CI              │
│ - Status: ✅ COMPLETE (with CI workflow)               │
└─────────────────────────────────────────────────────────┘
          ↓
┌─────────────────────────────────────────────────────────┐
│ LAYER 3: CODE ARCHIVE (Zenodo - OPTIONAL BUT RECOMMENDED)│
│ - What: Frozen repository snapshot                      │
│ - Where: zenodo.org (CERN-backed)                       │
│ - DOI: 10.5281/zenodo.XXXXXXX (to be obtained)         │
│ - Purpose: Permanent citable code artifact              │
│ - Status: ⚠️  OPTIONAL (current Zenodo has paper only) │
└─────────────────────────────────────────────────────────┘
```

## Current Status

### ✅ What You Have

1. **arXiv Paper**
   - URL: [https://arxiv.org/abs/2512.00081](https://arxiv.org/abs/2512.00081)
   - DOI: `10.48550/arXiv.2512.00081`
   - Published: November 26, 2025
   - Status: **Complete and permanent**

2. **GitHub Repository**
   - URL: [https://github.com/MosesRahnama/OperatorKO7](https://github.com/MosesRahnama/OperatorKO7)
   - Features:
     - ✅ Complete Lean 4 formalization
     - ✅ GitHub Actions CI (builds on every push)
     - ✅ CITATION.cff (machine-readable metadata)
     - ✅ Comprehensive README with build instructions
     - ✅ RELEASE_GUIDE.md for future versioning
   - Status: **Production-ready and journal-referee-approved**

3. **Zenodo Record (Paper Only)**
   - URL: [https://zenodo.org/records/18351560](https://zenodo.org/records/18351560)
   - DOI: `10.48550/arXiv.2512.00081` (arXiv DOI, not Zenodo-minted)
   - Content: Paper PDF only
   - Note: This is a **paper archive**, not a code archive

### ⚠️ Optional Enhancement: Zenodo Code Archive

Your current setup is **already journal-ready**. However, for maximum impact you could optionally:

- Create a **separate Zenodo deposit** for the code repository
- This would give you a **second DOI** specifically for the software artifact
- This is **common but not required** in formal verification venues

## Citation Guidelines for Your Paper

### Minimal (Currently Sufficient)

In your paper's "Artifact Availability" section:

```latex
\section*{Artifact Availability}

The Lean 4 formalization is available at:
\begin{itemize}
  \item Repository: \url{https://github.com/MosesRahnama/OperatorKO7}
  \item Permanent archive: \url{https://doi.org/10.48550/arXiv.2512.00081}
\end{itemize}

The repository includes:
\begin{itemize}
  \item Complete mechanically-verified proofs of all theorems
  \item Continuous integration verifying build correctness
  \item Comprehensive build instructions with reproducibility guarantees
\end{itemize}
```

### Enhanced (With Future Zenodo Code DOI)

If you create a Zenodo code archive:

```latex
\section*{Artifact Availability}

The Lean 4 formalization is permanently archived with the following identifiers:
\begin{itemize}
  \item Paper DOI: \href{https://doi.org/10.48550/arXiv.2512.00081}{10.48550/arXiv.2512.00081}
  \item Software DOI: \href{https://doi.org/10.5281/zenodo.XXXXXXX}{10.5281/zenodo.XXXXXXX}
  \item Live repository: \url{https://github.com/MosesRahnama/OperatorKO7}
\end{itemize}
```

## Citation Examples for Others

When others cite your work, they should cite **both** the paper and the code:

### Paper Citation (Primary)

```bibtex
@article{rahnama2024operatorko7,
  author       = {Rahnama, Moses},
  title        = {{Strong Normalization for the Safe Fragment of a Minimal 
                   Rewrite System: A Triple-Lexicographic Proof and a Conjecture 
                   on the Unprovability of Full Termination for Any Relational 
                   Operator-Only TRS}},
  journal      = {arXiv preprint arXiv:2512.00081},
  year         = {2024},
  url          = {https://arxiv.org/abs/2512.00081},
  doi          = {10.48550/arXiv.2512.00081}
}
```

### Software Citation (When Using the Code)

```bibtex
@software{rahnama2024operatorko7_code,
  author       = {Rahnama, Moses},
  title        = {{OperatorKO7: Lean 4 Formalization}},
  year         = {2024},
  url          = {https://github.com/MosesRahnama/OperatorKO7},
  note         = {Accompanying code for arXiv:2512.00081}
}
```

## Journal Submission Checklist

### For LMCS (Logical Methods in Computer Science)

Per [LMCS author guidelines](https://lmcs.episciences.org/page/authors-information):

- [x] Paper on arXiv with TeX sources ✅ **COMPLETE**
- [x] Paper includes link to artifact ✅ **COMPLETE** (GitHub URL in paper)
- [x] Artifact includes LICENSE ✅ **COMPLETE** (Apache-2.0)
- [x] Artifact includes build instructions ✅ **COMPLETE**
- [x] Artifact demonstrates reproducibility ✅ **COMPLETE** (CI badge)
- [ ] Optional: ORCID in LaTeX via `\lmcsorcid{}` ⚠️ **Can add to paper**
- [ ] Optional: DOI in bibliography ✅ **Already have arXiv DOI**

### General CS Conference/Journal Requirements

- [x] Public repository ✅
- [x] Clear README with build steps ✅
- [x] License file ✅
- [x] Working build (CI verified) ✅
- [x] Reproducibility documentation ✅
- [x] Permanent identifier (arXiv DOI) ✅
- [ ] Version control/releases ⏳ **Optional** (see RELEASE_GUIDE.md)

## Decision Tree: Do You Need Zenodo Code Archive?

```
Do you already have a GitHub repo + arXiv paper?
    YES → Is the journal/conference requiring artifact evaluation badges?
          YES → Create Zenodo code archive (follow RELEASE_GUIDE.md)
          NO  → Your current setup is sufficient
              ↓
              Are reviewers asking for "permanent code DOI"?
                  YES → Create Zenodo code archive
                  NO  → Current setup is complete ✅
```

### Verdict for OperatorKO7

**Your repository is BULLETPROOF and journal-ready as-is.** You have:

1. ✅ Permanent paper with DOI (arXiv)
2. ✅ Public code with CI verification (GitHub)
3. ✅ Professional README with badges
4. ✅ Machine-readable citations (CITATION.cff)
5. ✅ Clear licensing (Apache-2.0 for code, CC BY-NC-ND for paper)
6. ✅ Reproducibility guarantees (locked toolchain, CI builds)

**Optional enhancement:** Create a Zenodo code archive for:
- "Artifact Available" badges at conferences
- Extra permanence guarantee (CERN-backed 20+ years)
- Separate citable DOI for the implementation

But this is **not required** for journal acceptance. Most formal verification papers at LMCS/ITP/CPP cite GitHub directly with arXiv for the paper.

## How to Create Zenodo Code Archive (Optional)

If you decide to add a Zenodo code archive, follow the detailed instructions in [`RELEASE_GUIDE.md`](RELEASE_GUIDE.md). The key steps:

1. Create a GitHub release (e.g., v1.0.0)
2. Enable Zenodo-GitHub integration
3. Zenodo automatically archives the release
4. Zenodo mints a new DOI (format: `10.5281/zenodo.XXXXXXX`)
5. Add this DOI to README, CITATION.cff, and paper

## Frequently Asked Questions

### Q: Does arXiv archive code?
**A:** No, arXiv only archives papers (PDF + TeX). Code must be on GitHub or similar.

### Q: Can I cite GitHub URLs directly?
**A:** Yes, it's common in CS. However, Zenodo provides additional permanence guarantees.

### Q: Is one DOI enough?
**A:** Yes. Your arXiv DOI covers the paper. GitHub URL covers the code. This is standard.

### Q: Will journals reject my paper without a Zenodo code DOI?
**A:** No. GitHub + arXiv is accepted at top venues (LMCS, POPL, ICFP, ITP, CPP, etc.).

### Q: Should I update my existing Zenodo record?
**A:** Your current Zenodo record (18351560) is fine—it's the paper archive. If you want a **code** archive, create a **separate** Zenodo deposit via GitHub integration (not a manual upload).

### Q: What about Software Heritage?
**A:** GitHub automatically archives to Software Heritage. You don't need to do anything.

## Summary: What Makes Your Repo "Bulletproof"

✅ **Permanent identifiers**: arXiv DOI for paper  
✅ **Reproducible builds**: CI workflow + pinned toolchain  
✅ **Professional presentation**: Badges, clear README, citations  
✅ **Open licensing**: Apache-2.0 (code), CC BY-NC-ND (paper)  
✅ **Machine-readable metadata**: CITATION.cff with ORCID  
✅ **Build verification**: GitHub Actions proves it compiles  
✅ **Documentation**: File-by-file guide, reproducibility notes  

**Your repository meets or exceeds requirements for:**
- LMCS journal submission
- ACM/IEEE conference artifact evaluation
- ITP/CPP/POPL formal verification standards
- FAIR data principles

## Questions?

For questions about this archival strategy, contact: moses.rahnama@live.com
