import Atoms.ForMathlib.CategoryTheory.Subfunctor.Basic
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Image
import Atoms.Homotopical.PresheafSlice
import Atoms.Homotopical.EilenbergZilber.RigidCellularModel

open CategoryTheory Limits MorphismProperty
open CostructuredArrow (overMkIsoYoneda overMkIsoYoneda_naturality mono_left_iff
  isSplitEpi_left_iff)

namespace Atoms.Homotopical

section Generic

universe u w

variable {C : Type u} [Category.{w} C] {Y : Cᵒᵖ ⥤ Type w}

theorem IsAbsolutePushout.of_left {a b c d : CostructuredArrow yoneda Y} {f : a ⟶ b}
    {g : a ⟶ c} {h : b ⟶ d} {k : c ⟶ d}
    (sq : IsAbsolutePushout f.left g.left h.left k.left) : IsAbsolutePushout f g h k := by
  have hw : f ≫ h = g ≫ k := CostructuredArrow.hom_ext _ _ (by simpa using sq.w)
  have h₁ : IsPushout ((CostructuredArrow.toOver yoneda Y).map f)
      ((CostructuredArrow.toOver yoneda Y).map g) ((CostructuredArrow.toOver yoneda Y).map h)
      ((CostructuredArrow.toOver yoneda Y).map k) :=
    IsPushout.of_map (Over.forget Y) (by rw [← Functor.map_comp, ← Functor.map_comp, hw]) sq
  let φ := CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow Y
  exact (h₁.map (overEquivPresheafCostructuredArrow Y).functor).of_iso (φ.app a) (φ.app b)
    (φ.app c) (φ.app d) (φ.hom.naturality f) (φ.hom.naturality g) (φ.hom.naturality h)
    (φ.hom.naturality k)

instance EZCategory.costructuredArrow [EZCategory C] :
    EZCategory (CostructuredArrow yoneda Y) where
  deg x := EZCategory.deg x.left
  deg_le_of_mono f hf := EZCategory.deg_le_of_mono f.left ((mono_left_iff f).2 hf)
  isIso_of_mono_of_deg_eq f hf h := by
    have : IsIso ((CostructuredArrow.proj yoneda Y).map f) :=
      EZCategory.isIso_of_mono_of_deg_eq f.left ((mono_left_iff f).2 hf) h
    exact isIso_of_reflects_iso f (CostructuredArrow.proj yoneda Y)
  exists_factorization {x y} f := by
    obtain ⟨c, p, i, hp, hi, hpi⟩ := EZCategory.exists_factorization f.left
    let c' : CostructuredArrow yoneda Y := CostructuredArrow.mk (yoneda.map i ≫ y.hom)
    let p' : x ⟶ c' := CostructuredArrow.homMk p (by
      simp only [c', CostructuredArrow.mk_hom_eq_self]
      rw [← Functor.map_comp_assoc, hpi, CostructuredArrow.w f])
    let i' : c' ⟶ y := CostructuredArrow.homMk i rfl
    exact ⟨c', p', i', (isSplitEpi_left_iff p').1 hp, (mono_left_iff i').1 hi,
      CostructuredArrow.hom_ext _ _ (by simpa [p', i'] using hpi)⟩
  exists_absolutePushout {a b c} p q hp hq := by
    obtain ⟨d, p', q', sq⟩ := EZCategory.exists_absolutePushout p.left q.left
      ((isSplitEpi_left_iff p).2 hp) ((isSplitEpi_left_iff q).2 hq)
    have hw : yoneda.map p.left ≫ b.hom = yoneda.map q.left ≫ c.hom := by
      rw [CostructuredArrow.w p, CostructuredArrow.w q]
    let d' : CostructuredArrow yoneda Y := CostructuredArrow.mk (IsPushout.desc sq _ _ hw)
    let p'' : b ⟶ d' := CostructuredArrow.homMk p' (IsPushout.inl_desc sq _ _ hw)
    let q'' : c ⟶ d' := CostructuredArrow.homMk q' (IsPushout.inr_desc sq _ _ hw)
    exact ⟨d', p'', q'', IsAbsolutePushout.of_left sq⟩

instance HasTrivialAutomorphisms.costructuredArrow [HasTrivialAutomorphisms C] :
    HasTrivialAutomorphisms (CostructuredArrow yoneda Y) :=
  ⟨fun _ ↦ ⟨fun e₁ e₂ ↦ Iso.ext (CostructuredArrow.hom_ext _ _ (congrArg Iso.hom
    (Subsingleton.elim ((CostructuredArrow.proj yoneda Y).mapIso e₁)
      ((CostructuredArrow.proj yoneda Y).mapIso e₂))))⟩⟩

theorem EZCategory.nonempty_ezCategory_elements_op [EZCategory C] :
    ∀ X : Cᵒᵖ ⥤ Type w, Nonempty (EZCategory (X.Elements)ᵒᵖ) :=
  fun X ↦ ⟨EZCategory.ofEquivalence (CategoryOfElements.costructuredArrowYonedaEquivalence X)⟩

end Generic

universe v

variable {A : Type v} [SmallCategory A]

theorem range_sliceHom_boundaryInclusion {X : Aᵒᵖ ⥤ Type v} (x : CostructuredArrow yoneda X) :
    Subfunctor.range (sliceHom ((EZCategory.boundary x.left).ι) x.hom ≫
      (overMkIsoYoneda x).hom) = EZCategory.boundary x := by
  let E := overEquivPresheafCostructuredArrow X
  let ψ := fun t : CostructuredArrow yoneda X ↦ overMkIsoYoneda t
  change Subfunctor.range (sliceHom (EZCategory.boundary x.left).ι x.hom ≫ (ψ x).hom) = _
  ext ⟨s⟩ g
  have hb : g ∈ (EZCategory.boundary x).obj (Opposite.op s) ↔
      g.left ∈ (EZCategory.boundary x.left).obj (Opposite.op s.left) :=
    not_congr (isSplitEpi_left_iff g).symm
  rw [Subfunctor.range_obj, Set.mem_range, hb, Subfunctor.mem_iff_exists_comp_ι]
  let G : Over.mk s.hom ⟶ Over.mk x.hom := Over.homMk (yoneda.map g.left) (CostructuredArrow.w g)
  have hg : yoneda.map g = (ψ s).inv ≫ E.functor.map G ≫ (ψ x).hom := by
    rw [Iso.eq_inv_comp]
    exact (overMkIsoYoneda_naturality g).symm
  let I : Over.mk ((EZCategory.boundary x.left).ι ≫ x.hom) ⟶ Over.mk x.hom :=
    Over.homMk (EZCategory.boundary x.left).ι
  change (∃ u, (sliceHom (EZCategory.boundary x.left).ι x.hom ≫ (ψ x).hom).app _ u = g) ↔ _
  change (∃ u, (E.functor.map I ≫ (ψ x).hom).app _ u = g) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    have hU : yonedaEquiv.symm u ≫ E.functor.map I ≫ (ψ x).hom = yoneda.map g :=
      yonedaEquiv.injective (by
        rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        exact hu)
    let V := E.fullyFaithfulFunctor.preimage ((ψ s).hom ≫ yonedaEquiv.symm u)
    have hV : V ≫ I = G := by
      apply E.fullyFaithfulFunctor.map_injective
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, ← cancel_mono (ψ x).hom,
        Category.assoc, Category.assoc, hU, hg, Iso.hom_inv_id_assoc]
    refine ⟨V.left, ?_⟩
    simpa [I, G] using congrArg CommaMorphism.left hV
  · rintro ⟨W, hW⟩
    let V : Over.mk s.hom ⟶ Over.mk ((EZCategory.boundary x.left).ι ≫ x.hom) :=
      Over.homMk W (by
        change W ≫ (EZCategory.boundary x.left).ι ≫ x.hom = s.hom
        rw [← Category.assoc, hW]
        exact CostructuredArrow.w g)
    have hV : V ≫ I = G := Over.OverMorphism.ext (by simpa [V, I, G] using hW)
    refine ⟨yonedaEquiv ((ψ s).inv ≫ E.functor.map V), ?_⟩
    have hU : ((ψ s).inv ≫ E.functor.map V) ≫ E.functor.map I ≫ (ψ x).hom = yoneda.map g := by
      rw [hg, Category.assoc, ← Functor.map_comp_assoc, hV]
    rw [← yonedaEquiv_comp, hU, yonedaEquiv_yoneda_map]

noncomputable def boundaryInclusionSliceHomIso {X : Aᵒᵖ ⥤ Type v}
    (x : CostructuredArrow yoneda X) :
    Arrow.mk ((EZCategory.boundary x).ι) ≅
      Arrow.mk (sliceHom ((EZCategory.boundary x.left).ι) x.hom) :=
  haveI : Mono (sliceHom ((EZCategory.boundary x.left).ι) x.hom) :=
    (overEquivPresheafCostructuredArrow X).functor.map_mono (Over.homMk _)
  haveI : Mono (sliceHom ((EZCategory.boundary x.left).ι) x.hom ≫
      (overMkIsoYoneda x).hom) := mono_comp _ _
  Arrow.isoMk (Subfunctor.isoOfEq (range_sliceHom_boundaryInclusion x).symm ≪≫
      (asIso (Subfunctor.toRange (sliceHom ((EZCategory.boundary x.left).ι) x.hom ≫
        (overMkIsoYoneda x).hom))).symm) (overMkIsoYoneda x).symm (by
    rw [← cancel_mono (overMkIsoYoneda x).hom]
    change Subfunctor.homOfLe (range_sliceHom_boundaryInclusion x).ge ≫
        inv (Subfunctor.toRange (sliceHom ((EZCategory.boundary x.left).ι) x.hom ≫
          (overMkIsoYoneda x).hom)) ≫
        sliceHom ((EZCategory.boundary x.left).ι) x.hom ≫ (overMkIsoYoneda x).hom =
      (EZCategory.boundary x).ι ≫ (overMkIsoYoneda x).inv ≫ (overMkIsoYoneda x).hom
    rw [Iso.inv_hom_id, Category.comp_id, Subfunctor.inv_toRange_comp]
    exact Subfunctor.homOfLe_ι _)

end Atoms.Homotopical
