import Atoms.Diagrammatic.GrayTensor.Functor

open CategoryTheory Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem exists_tensor_presentation {X Y : DiagSet.{u}} {T : Atom}
    (z : diagram (grayTensor X Y) T) (hz : ¬ IsDegenerate (grayTensor X Y) z) :
    ∃ (U V : Atom) (x : diagram X U) (y : diagram Y V) (e : T ≅ Atom.grayTensor U V),
      ¬ IsDegenerate X x ∧ ¬ IsDegenerate Y y ∧
      z = (grayTensor X Y).map e.hom.op (grayTensorCell x y) := by
  rw [isDegenerate_iff_not_isNondegenerate, not_not] at hz
  obtain ⟨U', V', x', y', f, rfl⟩ := exists_eq_map_grayTensorCell z
  obtain ⟨S, p, m, hp, hm, rfl⟩ := exists_collapse_inclusion_factorization f
  obtain ⟨A, B, i, j, e, -, -, rfl⟩ := Atom.exists_iso_comp_grayTensorMap_of_isInclusionHom m hm
  obtain ⟨U, q, x, hq, hx, hqx⟩ :=
    Homotopical.EZCategory.exists_isNondegenerate X A (X.map i.op x')
  obtain ⟨V, r, y, hr, hy, hry⟩ :=
    Homotopical.EZCategory.exists_isNondegenerate Y B (Y.map j.op y')
  have hcell : (grayTensor X Y).map (Atom.grayTensorMap i j).op (grayTensorCell x' y') =
      (grayTensor X Y).map (Atom.grayTensorMap q r).op (grayTensorCell x y) := by
    rw [← grayTensorCell_restrict, ← grayTensorCell_restrict, hqx, hry]
  set c := p ≫ e.hom ≫ Atom.grayTensorMap q r
  have := isSplitEpi_of_isCollapseHom p hp
  have := isSplitEpi_of_isCollapseHom _ (Atom.isCollapseHom_grayTensorMap q r
    (@isCollapseHom_of_isSplitEpi _ _ q hq) (@isCollapseHom_of_isSplitEpi _ _ r hr))
  have hz' : (grayTensor X Y).map ((p ≫ e.hom) ≫ Atom.grayTensorMap i j).op
      (grayTensorCell x' y') = (grayTensor X Y).map c.op (grayTensorCell x y) := by
    simp only [c, op_comp, Functor.map_comp_apply, Category.assoc, hcell]
  have : IsIso c := hz c inferInstance ⟨_, hz'.symm⟩
  refine ⟨U, V, x, y, asIso c, fun h => (isDegenerate_iff_not_isNondegenerate X x).1 h hx,
    fun h => (isDegenerate_iff_not_isNondegenerate Y y).1 h hy, hz'⟩

end Atoms.Diagrammatic
