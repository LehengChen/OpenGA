import OpenGALib.Comparison.BishopGromov.RiccatiComparison
import OpenGALib.Comparison.BishopGromov.RadialRiccati
import OpenGALib.Comparison.BishopGromov.LaplacianComparison
import OpenGALib.Comparison.BishopGromov.VolumeComparison

/-!
# Bishop–Gromov

OpenGALib's own development — there is no upstream Bishop–Gromov; the borrowed
divergence-theorem layer is infrastructure, this chain is the contribution.

Proof chain (each layer reduces the next):

* `RiccatiComparison.lean` (Petersen Ch.9 Lemma 27.1) — the real-analytic ODE
  core: the model mean curvature `m_K = (n-1) s_K'/s_K` solves the Riccati
  equation, and any Riccati sub-solution is dominated by it. *Proved (0 sorry).*
* `RadialRiccati.lean` — the analytic half of the Laplacian comparison, built
  by *reusing the proved Bochner stack* (not new ODE/exp-map theory): under the
  eikonal equation `|∇f|² ≡ 1`, the Bochner–Weitzenböck identity collapses to
  the scalar Riccati sub-equation `∇f(Δf) + (Δf)²/(n-1) + (n-1)K ≤ 0`, the exact
  hypothesis `riccati_le_model` consumes. The eikonal kernel lemma is proved;
  the `(n-1)`-sharpened Cauchy–Schwarz on the radial-kernel Hessian is the one
  remaining analytic lemma.
* `LaplacianComparison.lean` (do Carmo Ch.10 §1 Thm 1.4) — `Δ_g r ≤ m_K`, the
  geometric reading of the Riccati comparison (mean curvature of geodesic
  spheres = `Δ_g r`), turning the Ricci bound into volume-element growth.
  *Stated; proof pending.*
* `VolumeComparison.lean` — the headline `bishopGromov_volume_comparison`,
  obtained by integrating the Laplacian comparison in geodesic polar
  coordinates (uses the migrated closed-manifold divergence theorem).
  *Stated; proof pending.*
-/
