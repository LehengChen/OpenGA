import OpenGALib.Comparison.BishopGromov.LaplacianComparison
import OpenGALib.Comparison.BishopGromov.VolumeComparison

/-!
# Bishop–Gromov

Proof chain (each layer reduces the next):

* `LaplacianComparison.lean` (do Carmo Ch.10 §1 Thm 1.4) — `Δ_g r ≤` model;
  the analytic bridge from the Ricci bound to volume-element growth. *Stated;
  proof pending.*
* `VolumeComparison.lean` — the headline `bishopGromov_volume_comparison`,
  obtained by integrating the Laplacian comparison in geodesic polar
  coordinates. *Stated; proof pending.*

Pending sibling: `RiccatiComparison.lean` (Petersen Lemma 27.1) — the
ODE-level comparison underlying `LaplacianComparison`.
-/
