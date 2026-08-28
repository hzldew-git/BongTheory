/- Orthogonal splitting at an anisotropic represented line. -/
import Bong.QuadraticSpace.OrthogonalExtension
import Bong.QuadraticSpace.OrthogonalSumDiagonal

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The orthogonal decomposition determined by an anisotropic vector whose
quadratic value is the coefficient of the distinguished scaled line. -/
noncomputable def scaledLineOrthogonalIsometry
    (q : QuadraticSpace K V) (x : V) (A : Kˣ)
    (hx : q.IsAnisotropic x)
    (hA : q.quadratic x = (A : K)) :
    Isometry
      ((scaledLine A).orthogonalSum
        (q.orthogonalSpace x hx))
      q where
  toLinearEquiv :=
    (lineOrthogonalLinearEquiv (q := q) (x := x)
      (anisotropic := hx)).symm
  map_bilin := by
    rintro ⟨a, y⟩ ⟨b, z⟩
    change q.bilin (a • x + (y : V)) (b • x + (z : V)) =
      (A : K) * a * b + q.bilin (y : V) (z : V)
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    have hz : q.bilin x (z : V) = 0 :=
      (q.mem_vectorOrthogonal_iff x z).1 z.property
    have hy' : q.bilin (y : V) x = 0 := by
      rw [q.isSymm.eq]
      exact (q.mem_vectorOrthogonal_iff x y).1 y.property
    rw [hz, hy', show q.bilin x x = q.quadratic x from rfl, hA]
    ring

end QuadraticSpace

end Bong
