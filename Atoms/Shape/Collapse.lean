import Atoms.Shape.Closure
import Atoms.Molecule.RegularComplex.CartesianFibre
import Mathlib.CategoryTheory.EpiMono

namespace Atoms.Shape

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

theorem isIso_of_isCollapseHom_of_dimension_eq {U V : Atom} (p : U ⟶ V) (hp : IsCollapseHom p)
    (hd : U.dimension = V.dimension) : CategoryTheory.IsIso p :=
  letI := Atom.functor_isFibered p
  isIso_of_bijective p (bijective_of_isAtom U.isAtom V.isAtom (Atom.isMap p) hp
    (by rw [U.krullDim_eq_dimension, V.krullDim_eq_dimension, hd]))

theorem exists_collapse_inclusion_factorization {U V : Atom} (f : U ⟶ V) :
    ∃ (W : Atom) (p : U ⟶ W) (i : W ⟶ V), IsCollapseHom p ∧ IsInclusionHom i ∧ p ≫ i = f := by
  refine ⟨Atom.ofClosure V (f U.top), principalLift V (f U.top) f (apply_mem_closure_apply_top f),
    Atom.closureIncl V _, fun w => ?_, Atom.isInclusionHom_closureIncl _ _,
    principalLift_comp_closureIncl _ _ _ _⟩
  obtain ⟨z, -, hz⟩ := (Atom.isMap f).fibration ((Atom.closureIso V (f U.top)).inv w).2
  refine ⟨z, Atom.isInclusionHom_closureIncl V (f U.top) ?_⟩
  rw [← ConcreteCategory.comp_apply, principalLift_comp_closureIncl, hz]
  rw [← Atom.closureIncl_closureIso V (f U.top), Iso.inv_hom_id_apply]

theorem collapse_inclusion_factorization_unique {U V W W' : Atom}
    (p : U ⟶ W) (i : W ⟶ V) (p' : U ⟶ W') (i' : W' ⟶ V)
    (hp : IsCollapseHom p) (hi : IsInclusionHom i) (hp' : IsCollapseHom p')
    (hi' : IsInclusionHom i') (hcomm : p ≫ i = p' ≫ i') :
    ∃! e : W ≅ W', p ≫ e.hom = p' ∧ e.hom ≫ i' = i := by
  have htop : p U.top = W.top := hp.apply_top
  have htop' : p' U.top = W'.top := hp'.apply_top
  have hiw : i W.top = i' W'.top := by
    rw [← htop, ← htop']
    exact ConcreteCategory.congr_hom hcomm U.top
  let l := principalLift V (i W.top) i (apply_mem_closure_apply_top i)
  let l' := principalLift V (i W.top) i' fun w => hiw.symm ▸ apply_mem_closure_apply_top i' w
  have := isIso_principalLift_of_isInclusionHom i hi
  have : IsIso l' := isIso_of_isInclusionHom_of_dimension_eq l'
    (fun a b hab => hi' (Subtype.mk.inj ((IsInclusion.injective
      (f := (Atom.closureIso V (i W.top)).hom)) hab)))
    (by rw [W'.dimension_eq, ← grade_eq_of_isInclusionHom i' hi', ← hiw, Atom.dimension_ofClosure])
  let e : W ≅ W' := asIso l ≪≫ (asIso l').symm
  have he2 : e.hom ≫ i' = i := by
    rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      (IsIso.inv_comp_eq l').2 (principalLift_comp_closureIncl _ _ _ _).symm,
      principalLift_comp_closureIncl]
  have he1 : p ≫ e.hom = p' := by
    have := mono_of_isInclusionHom i' hi'
    exact (cancel_mono i').1 (by rw [Category.assoc, he2, hcomm])
  refine ⟨e, ⟨he1, he2⟩, fun d hd => Iso.ext (Atom.hom_ext fun w => ?_)⟩
  obtain ⟨x, rfl⟩ := hp w
  exact ConcreteCategory.congr_hom (hd.1.trans he1.symm) x

theorem exists_section_closureIncl {U V : Atom} (p : U ⟶ V)
    {z : U.ogp} (hz : p z = V.top) (hmin : ∀ w < z, p w ≠ V.top) :
    ∃ s : V ⟶ U, s ≫ p = 𝟙 V ∧ ∀ w, w ≤ z → s (p w) = w := by
  have hdim : grade ℕ z = grade ℕ (p z) :=
    ((Atom.isMap p).minimal_fibre_iff z).1
      ⟨rfl, fun w hw hwz => (hwz.eq_or_lt.resolve_right fun hlt => hmin w hlt (hw.trans hz)).ge⟩
  let q : Atom.ofClosure U z ⟶ V := Atom.closureIncl U z ≫ p
  have hq : IsCollapseHom q := fun v => by
    obtain ⟨w, hwz, rfl⟩ := (Atom.isMap p).fibration (hz ▸ V.le_top v)
    obtain ⟨a, rfl⟩ := (Atom.exists_closureIncl_eq_iff U z w).2 hwz
    exact ⟨a, rfl⟩
  have hqd : (Atom.ofClosure U z).dimension = V.dimension := by
    rw [Atom.dimension_ofClosure, hdim, hz, V.dimension_eq]
  have := isIso_of_isCollapseHom_of_dimension_eq q hq hqd
  refine ⟨inv q ≫ Atom.closureIncl U z, by rw [Category.assoc, IsIso.inv_hom_id], fun w hw => ?_⟩
  obtain ⟨a, rfl⟩ := (Atom.exists_closureIncl_eq_iff U z w).2 hw
  exact congrArg (Atom.closureIncl U z) (ConcreteCategory.congr_hom (IsIso.hom_inv_id q) a)

theorem isSplitEpi_of_isCollapseHom {U V : Atom} (p : U ⟶ V) (hp : IsCollapseHom p) :
    CategoryTheory.IsSplitEpi p := by
  obtain ⟨z, hz, hmin⟩ := WellFounded.has_min wellFounded_lt {w | p w = V.top} (hp V.top)
  obtain ⟨s, hs, -⟩ := exists_section_closureIncl p hz fun w hw hpw => hmin w hpw hw
  exact IsSplitEpi.mk' ⟨s, hs⟩

theorem eq_of_isCollapseHom_of_forall_section_iff {U V : Atom} (p q : U ⟶ V)
    (hp : IsCollapseHom p) (h : ∀ s : V ⟶ U, s ≫ p = 𝟙 V ↔ s ≫ q = 𝟙 V) : p = q := by
  have := Atom.functor_isFibered p
  have := Atom.functor_isFibered q
  have htop : p U.top = V.top := hp.apply_top
  refine Atom.hom_ext (congrFun (IsMap.eq_of_forall_minimal_fibre_top U.isAtom.1
    (Atom.isMap p) (Atom.isMap q) U.le_top ?_).symm)
  intro z hz w hw
  rw [htop] at hz
  obtain ⟨s, hs, hsw⟩ := exists_section_closureIncl p hz.prop
    fun u hu hpu => hu.not_ge (hz.2 hpu hu.le)
  have := ConcreteCategory.congr_hom ((h s).1 hs) (p w)
  rwa [ConcreteCategory.comp_apply, hsw w hw, ConcreteCategory.id_apply] at this

theorem isInclusionHom_of_mono {U V : Atom} (f : U ⟶ V) [CategoryTheory.Mono f] :
    IsInclusionHom f := by
  obtain ⟨W, p, i, hp, hi, rfl⟩ := exists_collapse_inclusion_factorization f
  have := isSplitEpi_of_isCollapseHom p hp
  have hret : p ≫ section_ p = 𝟙 U :=
    (cancel_mono (p ≫ i)).1 (by
      rw [Category.id_comp, Category.assoc, ← Category.assoc (section_ p), IsSplitEpi.id,
        Category.id_comp])
  exact hi.comp (Function.LeftInverse.injective (ConcreteCategory.congr_hom hret))

theorem isCollapseHom_of_isSplitEpi {U V : Atom} (p : U ⟶ V) [IsSplitEpi p] :
    IsCollapseHom p :=
  fun y => ⟨section_ p y, ConcreteCategory.congr_hom (IsSplitEpi.id p) y⟩

theorem isCollapseHom_of_iso {U V : Atom} (e : U ≅ V) : IsCollapseHom e.hom :=
  isCollapseHom_of_isSplitEpi e.hom

theorem range_iso_hom_comp {V W U : Atom} (e : V ≅ W) (f : W ⟶ U) :
    Set.range (e.hom ≫ f) = Set.range f :=
  (isCollapseHom_of_iso e).range_comp f

theorem Atom.dimension_eq_of_iso {U V : Atom} (e : U ≅ V) :
    U.dimension = V.dimension :=
  le_antisymm (dimension_le_of_isCollapseHom e.inv (isCollapseHom_of_iso e.symm))
    (dimension_le_of_isCollapseHom e.hom (isCollapseHom_of_iso e))

theorem isCollapseHom_of_apply_eq_top {T U : Atom} (f : T ⟶ U) {t : T.ogp}
    (ht : f t = U.top) : IsCollapseHom f := fun y => by
  obtain ⟨s, -, hs⟩ := (Atom.isMap f).fibration (ht ▸ U.le_top y)
  exact ⟨s, hs⟩

theorem exists_iso_comp_closureIncl {T U : Atom} (g : T ⟶ U) {a : U.ogp}
    (h : Set.range g = Set.Iic a) (hd : T.dimension = grade ℕ a) :
    ∃ e : T ≅ Atom.ofClosure U a, e.hom ≫ Atom.closureIncl U a = g := by
  have hg : ∀ t, g t ∈ LowerSet.Iic a := fun t => by
    rw [LowerSet.mem_Iic_iff, ← Set.mem_Iic, ← h]
    exact Set.mem_range_self t
  have hcol : IsCollapseHom (principalLift U a g hg) := fun y => by
    obtain ⟨t, ht⟩ : Atom.closureIncl U a y ∈ Set.range g :=
      h.symm ▸ (closureIncl_mem_closure U a y : Atom.closureIncl U a y ∈ Set.Iic a)
    refine ⟨t, Atom.isInclusionHom_closureIncl U a ?_⟩
    rw [← ConcreteCategory.comp_apply, principalLift_comp_closureIncl, ht]
  have := isIso_of_isCollapseHom_of_dimension_eq _ hcol
    (hd.trans (Atom.dimension_ofClosure U a).symm)
  exact ⟨asIso (principalLift U a g hg), principalLift_comp_closureIncl U a g hg⟩

end Atoms.Shape
