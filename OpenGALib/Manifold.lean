import OpenGALib.Manifold.Charts.ChartedSpaceCore
import OpenGALib.Manifold.Charts.CoordinateBall
import OpenGALib.Manifold.Charts.PrecompactBasis
import OpenGALib.Manifold.Cutoff.Exhaustion
import OpenGALib.Manifold.Tangent.CurveVelocity
import OpenGALib.Manifold.Tangent.MFDeriv

/-!
# Manifold

Manifold-foundations domain: chart-level and atlas-level structure on
topological and smooth manifolds, stated directly on Mathlib's
`ChartedSpace` / `IsManifold` API. Sits below `Riemannian` in the library
layering. Currently provides coordinate-ball predicates for charts.
-/
