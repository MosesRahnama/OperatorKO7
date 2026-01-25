# Release and DOI Creation Guide

This guide walks you through creating a formal release (v1.0.0) and obtaining a permanent DOI via Zenodo for journal submission.

## Prerequisites

- ✅ Repository is journal-ready (CI workflow, CITATION.cff, enhanced README)
- ✅ Paper submitted to arXiv
- ✅ All code is finalized and ready for archival

## Step 1: Verify CI Build Status

Before creating a release, ensure the CI build is passing:

1. Go to [Actions tab](https://github.com/MosesRahnama/OperatorKO7/actions)
2. Verify the latest build shows a ✅ green checkmark
3. If red ❌, fix issues before proceeding

## Step 2: Create a Git Tag

### From Command Line (Recommended)

```bash
# Navigate to your local repository
cd /path/to/OperatorKO7

# Ensure you're on main and up-to-date
git checkout main
git pull origin main

# Create an annotated tag for v1.0.0
git tag -a v1.0.0 -m "Release v1.0.0: Formal verification of SafeStep termination (arXiv:2512.00081)"

# Push the tag to GitHub
git push origin v1.0.0
```

### From GitHub Web Interface (Alternative)

1. Go to [Releases page](https://github.com/MosesRahnama/OperatorKO7/releases)
2. Click "Draft a new release"
3. Click "Choose a tag" → type `v1.0.0` → click "Create new tag: v1.0.0 on publish"

## Step 3: Create GitHub Release

1. Go to [Releases page](https://github.com/MosesRahnama/OperatorKO7/releases)
2. Click "Draft a new release" (or continue from Step 2 if using web interface)
3. Fill in the form:

   **Tag:** `v1.0.0`
   
   **Release title:** `v1.0.0 - Formal Verification of SafeStep Termination`
   
   **Description:**
   ```markdown
   # OperatorKO7 v1.0.0
   
   This release contains the complete Lean 4 formalization accompanying the paper:
   
   > **OperatorKO7: Impossibility of Internal Termination Proofs for Full Relational Operator TRS**  
   > Moses Rahnama  
   > arXiv:2512.00081  
   > https://arxiv.org/abs/2512.00081
   
   ## What's Included
   
   - ✅ Mechanically-verified certified normalizer for SafeStep fragment
   - ✅ Strong normalization proof via triple-lexicographic measure
   - ✅ Confluence proof for safe fragment (Newman's lemma)
   - ✅ Impossibility catalog (machine-checked failure witnesses)
   - ✅ Continuous integration (GitHub Actions)
   - ✅ Reproducible build (pinned toolchain + dependencies)
   
   ## Build Instructions
   
   ```bash
   git clone https://github.com/MosesRahnama/OperatorKO7.git
   cd OperatorKO7
   git checkout v1.0.0
   lake exe cache get
   lake build
   ```
   
   ## Technical Specifications
   
   - **Lean version:** v4.22.0-rc4
   - **Commit hash:** [will be auto-filled by GitHub]
   - **Build verification:** [![Build Status](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml/badge.svg)](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml)
   
   ## Citation
   
   See [CITATION.cff](https://github.com/MosesRahnama/OperatorKO7/blob/v1.0.0/CITATION.cff) or use GitHub's "Cite this repository" feature.
   
   ## License
   
   - Lean code: Apache-2.0
   - Paper: CC BY-NC-ND 4.0
   ```

4. **Optional:** Attach the paper PDF
   - Click "Attach binaries" at the bottom
   - Upload `Paper/Rahnama_KO7_Submission.pdf`

5. **Set as latest release:** ✅ Check "Set as the latest release"

6. Click **"Publish release"**

## Step 4: Enable Zenodo Integration

### Initial Setup (One-time)

1. Go to [Zenodo GitHub integration](https://zenodo.org/account/settings/github/)
2. Log in with your GitHub account (or link accounts)
3. In the repository list, find `MosesRahnama/OperatorKO7`
4. Toggle the switch to **ON** (enable archival)

### Trigger Zenodo Archive

Zenodo automatically archives releases once integration is enabled:

- **If enabled BEFORE release:** Zenodo will automatically archive v1.0.0 within minutes
- **If enabled AFTER release:** You may need to create a new release (v1.0.1) or contact Zenodo support

### Monitor Zenodo Archive Status

1. Go to [Zenodo uploads](https://zenodo.org/deposit)
2. Wait 5-10 minutes for processing
3. Look for "MosesRahnama/OperatorKO7" in your uploads
4. Once processed, Zenodo will show a DOI badge

## Step 5: Update Repository with Zenodo DOI

Once Zenodo processes the archive, you'll receive a DOI (format: `10.5281/zenodo.XXXXXXX`)

### Update README Badge

Replace the "DOI pending" badge in README.md:

```markdown
# Before:
[![DOI](https://img.shields.io/badge/DOI-pending-orange)](https://github.com/MosesRahnama/OperatorKO7/releases)

# After:
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
```

### Update CITATION.cff

Add the DOI to `CITATION.cff`:

```yaml
version: "1.0.0"
date-released: "2026-01-25"  # Update to actual release date
doi: "10.5281/zenodo.XXXXXXX"  # Add this line
```

### Commit Changes

```bash
git add README.md CITATION.cff
git commit -m "Add Zenodo DOI badge and metadata"
git push origin main
```

## Step 6: Update Paper Submission

Add the Zenodo DOI to your paper:

1. **In the paper text:** Add a footnote or reference to the DOI
   ```
   The artifact is permanently archived at https://doi.org/10.5281/zenodo.XXXXXXX
   ```

2. **In bibliography:** Add an entry
   ```bibtex
   @software{rahnama2024operatorko7_artifact,
     author       = {Rahnama, Moses},
     title        = {{OperatorKO7: Mechanically-Verified Termination 
                      Proof for a Relational Operator TRS}},
     year         = {2024},
     publisher    = {Zenodo},
     version      = {v1.0.0},
     doi          = {10.5281/zenodo.XXXXXXX},
     url          = {https://doi.org/10.5281/zenodo.XXXXXXX}
   }
   ```

3. **Update arXiv:** If submitting a revised version, include the DOI

## Step 7: Verify Everything

### Checklist

- [ ] GitHub release v1.0.0 created with descriptive notes
- [ ] CI build badge shows ✅ green
- [ ] Zenodo DOI obtained and added to README
- [ ] CITATION.cff updated with DOI
- [ ] Paper references the permanent DOI
- [ ] Repository link in paper points to specific tag (not main branch)
- [ ] All badges in README are functional

### Test Reproducibility

Have a colleague (or fresh VM) test the build:

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
git checkout v1.0.0
lake exe cache get
lake build
# Should complete successfully
```

## Troubleshooting

### CI Build Fails

1. Check [Actions logs](https://github.com/MosesRahnama/OperatorKO7/actions)
2. Common issues:
   - Lean toolchain mismatch
   - Missing dependencies
   - Syntax errors

### Zenodo Not Archiving

1. Verify integration is enabled: [Zenodo GitHub settings](https://zenodo.org/account/settings/github/)
2. Check repository visibility (must be public)
3. Wait 15-30 minutes (Zenodo can be slow)
4. Contact Zenodo support if still not working

### DOI Badge Not Showing

1. Verify DOI format: `10.5281/zenodo.XXXXXXX`
2. Badge URL format:
   ```markdown
   [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
   ```

## Additional Resources

- [GitHub Releases Documentation](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases)
- [Zenodo GitHub Guide](https://help.zenodo.org/docs/github/archive-software/github-upload/)
- [CITATION.cff Documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-citation-files)
- [Semantic Versioning](https://semver.org/)

## Questions?

If you encounter issues during this process, contact: moses.rahnama@live.com
