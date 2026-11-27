# Finite-rank lower bounds for Property B

The four-page manuscript is `property-b.pdf`; its editable LaTeX source is `property-b.tex`. It is an AI-assisted research note attributed to Leo Gao, dated 27 November 2026, not a peer-reviewed publication.

Run `python verify_final.py` (Python 3). NumPy is optional, but recommended for the larger grids. There are no data files or external services to fetch. All probability comparisons that decide the bounds use integer or rational arithmetic. The expected output is `certificate_final.txt`. To reproduce it exactly on a Unix-like system:

    python verify_final.py > rerun.txt
    diff -u certificate_final.txt rerun.txt

To rebuild the manuscript on a standard TeX Live installation, run `pdflatex property-b.tex` twice. The release table compares with the Shanghai Innovation Institute's report of 17 November 2026; all lower bounds here are independently established by the included argument and verifier.
