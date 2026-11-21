import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Shape.Dual
import Atoms.Shape.SimplexFace

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape.Atom

@[implicit_reducible] def grayTensor (U V : Atom) : Atom :=
  Atom.ofOGP (grayProduct U.ogp V.ogp) (isAtom_grayProduct U.isAtom V.isAtom)

def grayTensorIso (U V : Atom) : grayProduct U.ogp V.ogp ≅ (grayTensor U V).ogp :=
  FiniteOGP.ofOGPIso _

def grayTensorMap {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    grayTensor U V ⟶ grayTensor U' V' :=
  letI := Atom.functor_isFibered f
  letI := Atom.functor_isFibered g
  letI := functor_isFibered_prodMap (Atom.isMap f).monotone (Atom.isMap g).monotone
    (isMap_prodMap U.isRDC U'.isRDC V.isRDC V'.isRDC (Atom.isMap f) (Atom.isMap g)).monotone
  Atom.conjHom (grayTensorIso U V) (grayTensorIso U' V') (fun p => (f p.1, g p.2))
    (isMap_prodMap U.isRDC U'.isRDC V.isRDC V'.isRDC (Atom.isMap f) (Atom.isMap g))

@[simp] theorem grayTensorMap_apply {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V')
    (z : (grayTensor U V).ogp) :
    grayTensorMap f g z =
      (grayTensorIso U' V').hom (f ((grayTensorIso U V).inv z).1,
        g ((grayTensorIso U V).inv z).2) := rfl

@[simp] theorem grayTensorMap_id (U V : Atom) :
    grayTensorMap (𝟙 U) (𝟙 V) = 𝟙 (grayTensor U V) := by
  ext z
  exact ConcreteCategory.congr_hom (grayTensorIso U V).inv_hom_id z

@[reassoc] theorem grayTensorMap_comp {U V U' V' U'' V'' : Atom}
    (f : U ⟶ U') (g : V ⟶ V') (f' : U' ⟶ U'') (g' : V' ⟶ V'') :
    grayTensorMap f g ≫ grayTensorMap f' g' = grayTensorMap (f ≫ f') (g ≫ g') := by
  ext z
  change (grayTensorIso U'' V'').hom
    (f' ((grayTensorIso U' V').inv ((grayTensorIso U' V').hom
      (f ((grayTensorIso U V).inv z).1, g ((grayTensorIso U V).inv z).2))).1,
     g' ((grayTensorIso U' V').inv ((grayTensorIso U' V').hom
      (f ((grayTensorIso U V).inv z).1, g ((grayTensorIso U V).inv z).2))).2) = _
  simp only [Iso.hom_inv_id_apply]
  rfl

@[implicit_reducible, simps obj] def grayTensorFunctor : Atom × Atom ⥤ Atom where
  obj p := grayTensor p.1 p.2
  map f := grayTensorMap f.1 f.2
  map_id p := grayTensorMap_id p.1 p.2
  map_comp f g := (grayTensorMap_comp f.1 f.2 g.1 g.2).symm

theorem isInclusionHom_grayTensorMap {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V')
    (hf : IsInclusionHom f) (hg : IsInclusionHom g) : IsInclusionHom (grayTensorMap f g) := by
  intro x y h
  apply (IsInclusion.injective (f := (grayTensorIso U V).inv))
  apply Prod.ext
  · apply hf
    exact congrArg Prod.fst ((IsInclusion.injective (f := (grayTensorIso U' V').hom)) h)
  · apply hg
    exact congrArg Prod.snd ((IsInclusion.injective (f := (grayTensorIso U' V').hom)) h)

theorem isCollapseHom_grayTensorMap {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V')
    (hf : IsCollapseHom f) (hg : IsCollapseHom g) : IsCollapseHom (grayTensorMap f g) := by
  intro z
  obtain ⟨x, hx⟩ := hf ((grayTensorIso U' V').inv z).1
  obtain ⟨y, hy⟩ := hg ((grayTensorIso U' V').inv z).2
  refine ⟨(grayTensorIso U V).hom (x, y), ?_⟩
  simp only [grayTensorMap_apply, Iso.hom_inv_id_apply]
  rw [hx, hy]
  exact ConcreteCategory.congr_hom (grayTensorIso U' V').inv_hom_id z

theorem dimension_grayTensor (U V : Atom) :
    (grayTensor U V).dimension = U.dimension + V.dimension := by
  have h : krullDim (grayTensor U V).ogp = (U.dimension + V.dimension : ℕ) := by
    rw [← krullDim_eq_of_orderIso (orderIsoOfIso (grayTensorIso U V)),
      krullDim_grayProduct U.krullDim_eq_dimension V.krullDim_eq_dimension]
  exact_mod_cast (grayTensor U V).krullDim_eq_dimension.symm.trans h

private theorem exists_grayTensorMap_closureIncl_eq {U V : Atom} (v : U.ogp) (w : V.ogp)
    (z : (grayTensor U V).ogp) (h : ((grayTensorIso U V).inv z).1 ≤ v)
    (h' : ((grayTensorIso U V).inv z).2 ≤ w) :
    ∃ t, grayTensorMap (Atom.closureIncl U v) (Atom.closureIncl V w) t = z := by
  obtain ⟨a, ha⟩ := (Atom.exists_closureIncl_eq_iff U v _).2 h
  obtain ⟨b, hb⟩ := (Atom.exists_closureIncl_eq_iff V w _).2 h'
  refine ⟨(grayTensorIso _ _).hom (a, b), ?_⟩
  rw [grayTensorMap_apply, Iso.hom_inv_id_apply, ha, hb]
  exact ConcreteCategory.congr_hom (grayTensorIso U V).inv_hom_id z

theorem exists_iso_comp_grayTensorMap_of_isInclusionHom {S U V : Atom}
    (m : S ⟶ grayTensor U V) (hm : IsInclusionHom m) :
    ∃ (A B : Atom) (i : A ⟶ U) (j : B ⟶ V) (e : S ≅ grayTensor A B),
      IsInclusionHom i ∧ IsInclusionHom j ∧ e.hom ≫ grayTensorMap i j = m := by
  set v := ((grayTensorIso U V).inv (m S.top)).1
  set w := ((grayTensorIso U V).inv (m S.top)).2
  set g := grayTensorMap (Atom.closureIncl U v) (Atom.closureIncl V w)
  have hg : IsInclusionHom g := isInclusionHom_grayTensorMap _ _
    (Atom.isInclusionHom_closureIncl U v) (Atom.isInclusionHom_closureIncl V w)
  obtain ⟨h, hh⟩ := exists_comp_eq_of_isInclusionHom g hg m fun t => by
    have hle : (grayTensorIso U V).inv (m t) ≤ (grayTensorIso U V).inv (m S.top) :=
      (isMorphism (grayTensorIso U V).inv).monotone ((Atom.isMap m).monotone (S.le_top t))
    exact exists_grayTensorMap_closureIncl_eq v w (m t) hle.1 hle.2
  obtain ⟨k, hk⟩ := exists_comp_eq_of_isInclusionHom m hm g fun t => by
    have hle : g t ≤ m S.top := by
      rw [grayTensorMap_apply]
      refine ((isMorphism (grayTensorIso U V).hom).monotone ⟨?_, ?_⟩).trans_eq
        (ConcreteCategory.congr_hom (grayTensorIso U V).inv_hom_id (m S.top))
      · exact closureIncl_mem_closure U v _
      · exact closureIncl_mem_closure V w _
    obtain ⟨s, -, hs⟩ := (Atom.isMap m).fibration hle
    exact ⟨s, hs⟩
  have := mono_of_isInclusionHom m hm
  have := mono_of_isInclusionHom g hg
  refine ⟨_, _, _, _, ⟨h, k, ?_, ?_⟩, Atom.isInclusionHom_closureIncl U v,
    Atom.isInclusionHom_closureIncl V w, hh⟩
  · exact (cancel_mono m).1 (by rw [Category.assoc, hk, hh, Category.id_comp])
  · exact (cancel_mono g).1 (by rw [Category.assoc, hh, hk, Category.id_comp])

theorem grayTensorIso_inv_top (U V : Atom) :
    (grayTensorIso U V).inv (grayTensor U V).top = (U.top, V.top) :=
  le_antisymm (Prod.le_def.2 ⟨U.le_top _, V.le_top _⟩)
    ((orderIsoOfIso (grayTensorIso U V)).le_symm_apply.2 ((grayTensor U V).le_top _))

theorem grayTensorIso_inv_grayTensorMap_top {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    (grayTensorIso U' V').inv (grayTensorMap f g (grayTensor U V).top) = (f U.top, g V.top) := by
  rw [grayTensorMap_apply, Iso.hom_inv_id_apply, grayTensorIso_inv_top]

theorem le_iff_grayTensorIso_inv {U V : Atom} (z w : (grayTensor U V).ogp) :
    z ≤ w ↔ ((grayTensorIso U V).inv z).1 ≤ ((grayTensorIso U V).inv w).1 ∧
      ((grayTensorIso U V).inv z).2 ≤ ((grayTensorIso U V).inv w).2 :=
  (orderIsoOfIso (grayTensorIso U V)).symm.le_iff_le.symm

theorem mem_boundary_Iic_grayTensor_iff {U V : Atom} (z w : (grayTensor U V).ogp) (n : ℕ)
    (α : Bool) :
    z ∈ (grayTensor U V).ogp.boundary (.Iic w) n α ↔
      ∃ k ≤ n, ((grayTensorIso U V).inv z).1 ∈
          U.ogp.boundary (.Iic ((grayTensorIso U V).inv w).1) k α ∧
        ((grayTensorIso U V).inv z).2 ∈
          V.ogp.boundary (.Iic ((grayTensorIso U V).inv w).2) (n - k) (xor k.bodd α) := by
  rw [← apply_mem_map_iff (grayTensorIso U V).inv, map_boundary, map_Iic]
  exact mem_boundary_Iic_grayProduct U.isRDC V.isRDC _ _ n α _ _

section Square

private theorem boundary_Iic_zero_atomSimplex_zero (x : (atomSimplex 0).ogp) (α : Bool) :
    (atomSimplex 0).ogp.boundary (.Iic x) 0 α = .Iic x :=
  boundary_eq_self (by
    rw [LowerSet.krullDim_Iic]
    exact_mod_cast (dimension_atomSimplex 0) ▸ (atomSimplex 0).grade_le_dimension x) α

abbrev squareSide (γ : Bool) (i : Fin 2) : (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp :=
  cond γ
    (grayTensorMap (𝟙 (atomSimplex 1)) (simplexHom (SimplexCategory.δ i).toOrderHom)
      (grayTensor (atomSimplex 1) (atomSimplex 0)).top)
    (grayTensorMap (simplexHom (SimplexCategory.δ i).toOrderHom) (𝟙 (atomSimplex 1))
      (grayTensor (atomSimplex 0) (atomSimplex 1)).top)

private theorem mem_boundary_square_iff (α : Bool)
    (z : (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp) :
    z ∈ (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp.boundary ⊤ 1 α ↔
      z ≤ squareSide α 1 ∨ z ≤ squareSide (!α) 0 := by
  rw [← Atom.Iic_top, mem_boundary_Iic_grayTensor_iff, grayTensorIso_inv_top,
    (atomSimplex 1).Iic_top]
  cases α <;>
  simp only [Nat.le_one_iff_eq_zero_or_eq_one, or_and_right, exists_or, exists_eq_left,
    le_iff_grayTensorIso_inv, grayTensorIso_inv_grayTensorMap_top, Nat.sub_zero, Nat.sub_self,
    Nat.bodd_zero, Nat.bodd_one, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true,
    boundary_univ_one_atomSimplex_one, boundary_univ_zero_atomSimplex_one, cond_false, cond_true,
    SimplexCategory.len_mk, LowerSet.mem_top, LowerSet.mem_Iic_iff, id_apply, Atom.le_top,
    and_true, true_and]
  exact or_comm

private theorem mem_boundary_squareSide_one_iff (α : Bool)
    (z : (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp) :
    z ∈ (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp.boundary (.Iic (squareSide α 1)) 0
        true ↔
      z ≤ squareSide α 1 ∧ z ≤ squareSide (!α) 0 := by
  rw [mem_boundary_Iic_grayTensor_iff]
  cases α <;>
  simp only [Nat.le_zero, exists_eq_left, Nat.sub_self,
    Nat.bodd_zero, Bool.false_xor, le_iff_grayTensorIso_inv, grayTensorIso_inv_grayTensorMap_top,
    SimplexCategory.len_mk, id_apply, (atomSimplex 1).Iic_top, boundary_univ_zero_atomSimplex_one,
    cond_true, cond_false, Bool.not_false, Bool.not_true, LowerSet.mem_Iic_iff, Atom.le_top,
    and_true, true_and] <;>
  rw [boundary_Iic_simplexHom_δ_atomSimplex_one, LowerSet.mem_Iic_iff]
  exact and_comm

private theorem mem_boundary_squareSide_zero_iff (α : Bool)
    (z : (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp) :
    z ∈ (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp.boundary (.Iic (squareSide (!α) 0)) 0
        false ↔
      z ≤ squareSide α 1 ∧ z ≤ squareSide (!α) 0 := by
  rw [mem_boundary_Iic_grayTensor_iff]
  cases α <;>
  simp only [Nat.le_zero, exists_eq_left, Nat.sub_self,
    Nat.bodd_zero, Bool.false_xor, le_iff_grayTensorIso_inv, grayTensorIso_inv_grayTensorMap_top,
    SimplexCategory.len_mk, id_apply, (atomSimplex 1).Iic_top, boundary_univ_zero_atomSimplex_one,
    cond_true, cond_false, Bool.not_false, Bool.not_true, LowerSet.mem_Iic_iff, Atom.le_top,
    and_true, true_and] <;>
  rw [boundary_Iic_simplexHom_δ_atomSimplex_one, LowerSet.mem_Iic_iff]
  exact and_comm

theorem isPastingIn_boundary_square (α : Bool) :
    (grayTensor (atomSimplex 1) (atomSimplex 1)).ogp.IsPastingIn 0 (.Iic (squareSide α 1))
      (.Iic (squareSide (!α) 0))
      ((grayTensor (atomSimplex 1) (atomSimplex 1)).ogp.boundary ⊤ 1 α) where
  sup_eq := SetLike.ext fun z => by
    rw [LowerSet.mem_sup_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff,
      mem_boundary_square_iff]
  inf_eq_output := SetLike.ext fun z => by
    rw [LowerSet.mem_inf_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff,
      mem_boundary_squareSide_one_iff]
  inf_eq_input := SetLike.ext fun z => by
    rw [LowerSet.mem_inf_iff, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff,
      mem_boundary_squareSide_zero_iff]

private theorem mem_boundary_grayTensor_atomSimplex_zero_one_iff (α : Bool)
    (z : (grayTensor (atomSimplex 0) (atomSimplex 1)).ogp) :
    z ∈ (grayTensor (atomSimplex 0) (atomSimplex 1)).ogp.boundary ⊤ 0 α ↔
      z ≤ grayTensorMap (𝟙 (atomSimplex 0))
        (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom)
          (grayTensor (atomSimplex 0) (atomSimplex 0)).top := by
  rw [← Atom.Iic_top, mem_boundary_Iic_grayTensor_iff, le_iff_grayTensorIso_inv,
    grayTensorIso_inv_grayTensorMap_top, grayTensorIso_inv_top, (atomSimplex 1).Iic_top]
  simp only [Nat.le_zero, exists_eq_left, Nat.sub_self, Nat.bodd_zero, Bool.false_xor,
    SimplexCategory.len_mk, boundary_Iic_zero_atomSimplex_zero, boundary_univ_zero_atomSimplex_one,
    LowerSet.mem_Iic_iff, id_apply, Atom.le_top, true_and]

private theorem mem_boundary_grayTensor_atomSimplex_one_zero_iff (α : Bool)
    (z : (grayTensor (atomSimplex 1) (atomSimplex 0)).ogp) :
    z ∈ (grayTensor (atomSimplex 1) (atomSimplex 0)).ogp.boundary ⊤ 0 α ↔
      z ≤ grayTensorMap (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom)
        (𝟙 (atomSimplex 0)) (grayTensor (atomSimplex 0) (atomSimplex 0)).top := by
  rw [← Atom.Iic_top, mem_boundary_Iic_grayTensor_iff, le_iff_grayTensorIso_inv,
    grayTensorIso_inv_grayTensorMap_top, grayTensorIso_inv_top, (atomSimplex 1).Iic_top]
  simp only [Nat.le_zero, exists_eq_left, Nat.sub_self, Nat.bodd_zero, Bool.false_xor,
    SimplexCategory.len_mk, boundary_Iic_zero_atomSimplex_zero, boundary_univ_zero_atomSimplex_one,
    LowerSet.mem_Iic_iff, id_apply, Atom.le_top]

theorem boundary_grayTensor_atomSimplex_zero_one (α : Bool) :
    (grayTensor (atomSimplex 0) (atomSimplex 1)).ogp.boundary ⊤ 0 α =
      .Iic (grayTensorMap (𝟙 (atomSimplex 0))
        (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom)
          (grayTensor (atomSimplex 0) (atomSimplex 0)).top) :=
  SetLike.ext fun z => (mem_boundary_grayTensor_atomSimplex_zero_one_iff α z).trans
    LowerSet.mem_Iic_iff.symm

theorem boundary_grayTensor_atomSimplex_one_zero (α : Bool) :
    (grayTensor (atomSimplex 1) (atomSimplex 0)).ogp.boundary ⊤ 0 α =
      .Iic (grayTensorMap (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom)
        (𝟙 (atomSimplex 0)) (grayTensor (atomSimplex 0) (atomSimplex 0)).top) :=
  SetLike.ext fun z => (mem_boundary_grayTensor_atomSimplex_one_zero_iff α z).trans
    LowerSet.mem_Iic_iff.symm

end Square

section Dual

def grayTensorDualIso (U V : Atom) :
    (grayTensor U V).dual Nat.bodd ≅ grayTensor (V.dual Nat.bodd) (U.dual Nat.bodd) :=
  isoOfIso (((grayTensor U V).toMoleculeShape.dualIso Nat.bodd).symm ≪≫
    (OGP.dualFunctor Nat.bodd).mapIso (grayTensorIso U V).symm ≪≫ grayProductSwap U.ogp V.ogp ≪≫
    MonoidalCategory.tensorIso (V.toMoleculeShape.dualIso Nat.bodd)
      (U.toMoleculeShape.dualIso Nat.bodd) ≪≫ grayTensorIso (V.dual Nat.bodd) (U.dual Nat.bodd))

@[simp] theorem grayTensorDualIso_hom_apply (U V : Atom)
    (z : ((grayTensor U V).dual Nat.bodd).ogp) :
    (grayTensorDualIso U V).hom z = (grayTensorIso (V.dual Nat.bodd) (U.dual Nat.bodd)).hom
      ((V.toMoleculeShape.dualIso Nat.bodd).hom ((grayTensorIso U V).inv
          (((grayTensor U V).toMoleculeShape.dualIso Nat.bodd).inv z)).2,
        (U.toMoleculeShape.dualIso Nat.bodd).hom ((grayTensorIso U V).inv
          (((grayTensor U V).toMoleculeShape.dualIso Nat.bodd).inv z)).1) :=
  rfl

@[reassoc]
theorem grayTensorDualIso_hom_naturality {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    dualMap Nat.bodd (grayTensorMap f g) ≫ (grayTensorDualIso U' V').hom =
      (grayTensorDualIso U V).hom ≫ grayTensorMap (dualMap Nat.bodd g) (dualMap Nat.bodd f) :=
  hom_ext fun z => by
    simp only [ConcreteCategory.comp_apply, grayTensorDualIso_hom_apply, dualMap_apply,
      grayTensorMap_apply, Iso.hom_inv_id_apply]

@[reassoc]
theorem dualMap_grayTensorDualIso_hom_comp (U V : Atom) :
    dualMap Nat.bodd (grayTensorDualIso U V).hom ≫
        (grayTensorDualIso (V.dual Nat.bodd) (U.dual Nat.bodd)).hom ≫
          grayTensorMap (dualDualIso Nat.bodd U).hom (dualDualIso Nat.bodd V).hom =
      (dualDualIso Nat.bodd (grayTensor U V)).hom :=
  hom_ext fun z => by
    simp only [ConcreteCategory.comp_apply, grayTensorDualIso_hom_apply, dualMap_apply,
      grayTensorMap_apply, dualDualIso_hom_apply, Iso.hom_inv_id_apply, Iso.inv_hom_id_apply,
      Prod.mk.eta]

end Dual

end Atoms.Shape.Atom
