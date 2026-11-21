import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Atoms.TestCategory.Simplicial.Contraction
import Atoms.TestCategory.Simplicial.OrdinaryNerveElements
import Atoms.TestCategory.Presheaf.Product

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty

universe u

namespace Atoms.TestCategory

section Bisimplicial

open MonoidalCategory

def bisimplicialShape (A : Type u) [SmallCategory A] :
    A × (AsSmall.{u} SimplexCategory) ⥤ SSet.{u} :=
  ((Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor).prod
    (AsSmall.down ⋙ SSet.stdSimplex)) ⋙
    MonoidalCategory.tensor SSet.{u}

def bisimplicialShapeFst (A : Type u) [SmallCategory A] :
    bisimplicialShape A ⟶
      CategoryTheory.Prod.fst A (AsSmall.{u} SimplexCategory) ⋙
        Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor where
  app p := CartesianMonoidalCategory.fst _ _
  naturality p q f := by
    change (CategoryTheory.nerveFunctor.map ((Over.mapFunctor A).map f.1) ⊗ₘ
        SSet.stdSimplex.map f.2.down) ≫ CartesianMonoidalCategory.fst _ _ =
      CartesianMonoidalCategory.fst _ _ ≫
        CategoryTheory.nerveFunctor.map ((Over.mapFunctor A).map f.1)
    exact CartesianMonoidalCategory.tensorHom_fst _ _

def bisimplicialShapeSnd (A : Type u) [SmallCategory A] :
    bisimplicialShape A ⟶
      CategoryTheory.Prod.snd A (AsSmall.{u} SimplexCategory) ⋙
        AsSmall.down ⋙ SSet.stdSimplex where
  app p := CartesianMonoidalCategory.snd _ _
  naturality p q f := by
    change (CategoryTheory.nerveFunctor.map ((Over.mapFunctor A).map f.1) ⊗ₘ
        SSet.stdSimplex.map f.2.down) ≫ CartesianMonoidalCategory.snd _ _ =
      CartesianMonoidalCategory.snd _ _ ≫ SSet.stdSimplex.map f.2.down
    exact CartesianMonoidalCategory.tensorHom_snd _ _

def stdSimplexRestrictionIso :
    simplicialRestriction (AsSmall.down ⋙ SSet.stdSimplex) ≅ SSet.asSmall :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun n => (SSet.yonedaEquiv (X := X) (n := (ULift.down n.unop))).toIso)
      (by
        intro m n g
        ext h
        exact (SSet.yonedaEquiv_naturality g.unop.down h).symm))
    (by
      intro X Y f
      ext n h
      exact SSet.yonedaEquiv_comp h f)

namespace BasicLocalizer

theorem wPsh_simplicialRestriction_stdSimplex_map_iff
    (𝒲 : BasicLocalizer.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    𝒲.wPsh (AsSmall.{u} SimplexCategory)
      ((simplicialRestriction (AsSmall.down ⋙ SSet.stdSimplex)).map f) ↔
      𝒲.wSSet f := by
  let e := stdSimplexRestrictionIso
  have hK : 𝒲.wPsh (AsSmall.{u} SimplexCategory) (e.hom.app K) :=
    isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _)
  have hL : 𝒲.wPsh (AsSmall.{u} SimplexCategory) (e.hom.app L) :=
    isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (isomorphisms.infer_property _)
  constructor
  · intro hf
    have hc := (𝒲.wPsh (AsSmall.{u} SimplexCategory)).comp_mem _ _ hf hL
    rw [e.hom.naturality f] at hc
    exact (𝒲.wPsh (AsSmall.{u} SimplexCategory)).of_precomp _ _ hK hc
  · intro hf
    have hc := (𝒲.wPsh (AsSmall.{u} SimplexCategory)).comp_mem _ _ hK hf
    change 𝒲.wPsh (AsSmall.{u} SimplexCategory) (e.hom.app K ≫ SSet.asSmall.map f) at hc
    rw [← e.hom.naturality f] at hc
    exact (𝒲.wPsh (AsSmall.{u} SimplexCategory)).of_postcomp _ _ hL hc

theorem locallyAspherical_restriction_stdSimplex (𝒲 : BasicLocalizer.{u}) :
    𝒲.LocallyAspherical (AsSmall.{u} SimplexCategory)
      ((simplicialRestriction (AsSmall.down ⋙ SSet.stdSimplex)).obj Δ[1]) := by
  intro a
  exact (𝒲.pshAspherical_iff_of_iso _
    (prod.mapIso (Iso.refl _) (stdSimplexRestrictionIso.app Δ[1])).symm).1
    (𝒲.locallyAspherical_asSmall_stdSimplex_one a)

end BasicLocalizer

def restrictionDeformationHomotopy {C : Type u} [SmallCategory C]
    {k k' : C ⥤ SSet.{u}} (π : k' ⟶ k)
    (H : k' ⋙ tensorLeft Δ[1] ⟶ k') (X : SSet.{u}) :
    ((simplicialRestriction k).obj Δ[1]) ⊗
      ((simplicialRestriction k').obj X) ⟶ (simplicialRestriction k').obj X where
  app c := ↾fun p => CartesianMonoidalCategory.lift (π.app c.unop ≫ p.1) (𝟙 _) ≫
    H.app c.unop ≫ p.2
  naturality c d f := by
    ext p
    change (CartesianMonoidalCategory.lift
      (π.app d.unop ≫ k.map f.unop ≫ p.1) (𝟙 _) ≫ H.app d.unop ≫
        k'.map f.unop ≫ p.2) =
      (k'.map f.unop ≫ CartesianMonoidalCategory.lift
        (π.app c.unop ≫ p.1) (𝟙 _) ≫ H.app c.unop ≫ p.2)
    have hπ := π.naturality f.unop
    have hH := H.naturality f.unop
    change (𝟙 Δ[1] ⊗ₘ k'.map f.unop) ≫ H.app c.unop =
      H.app d.unop ≫ k'.map f.unop at hH
    have hlift : CartesianMonoidalCategory.lift
        (π.app d.unop ≫ k.map f.unop ≫ p.1) (𝟙 _) ≫
          (𝟙 Δ[1] ⊗ₘ k'.map f.unop) =
        k'.map f.unop ≫ CartesianMonoidalCategory.lift
          (π.app c.unop ≫ p.1) (𝟙 _) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
        exact congrArg (fun z => z ≫ p.1) hπ.symm
      · cat_disch
    calc
      _ = (CartesianMonoidalCategory.lift
          (π.app d.unop ≫ k.map f.unop ≫ p.1) (𝟙 _) ≫
            (H.app d.unop ≫ k'.map f.unop)) ≫ p.2 := by
              cat_disch
      _ = (CartesianMonoidalCategory.lift
          (π.app d.unop ≫ k.map f.unop ≫ p.1) (𝟙 _) ≫
            ((𝟙 Δ[1] ⊗ₘ k'.map f.unop) ≫ H.app c.unop)) ≫ p.2 := by rw [hH]
      _ = _ := by
        calc
          _ = ((CartesianMonoidalCategory.lift
              (π.app d.unop ≫ k.map f.unop ≫ p.1) (𝟙 _) ≫
                (𝟙 Δ[1] ⊗ₘ k'.map f.unop)) ≫ H.app c.unop) ≫ p.2 := by cat_disch
          _ = ((k'.map f.unop ≫ CartesianMonoidalCategory.lift
              (π.app c.unop ≫ p.1) (𝟙 _)) ≫ H.app c.unop) ≫ p.2 :=
                congrArg (fun z => (z ≫ H.app c.unop) ≫ p.2) hlift
          _ = _ := by cat_disch

def restrictionDeformationSection {C : Type u} [SmallCategory C]
    {k k' : C ⥤ SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ Δ[1]) (X : SSet.{u}) :
    (simplicialRestriction k').obj X ⟶
      ((simplicialRestriction k).obj Δ[1]) ⊗
        ((simplicialRestriction k').obj X) := by
  let ν : (simplicialRestriction k').obj X ⟶
      (simplicialRestriction k).obj Δ[1] :=
    { app c := ↾fun _ => CartesianMonoidalCategory.toUnit (k.obj c.unop) ≫ v
      naturality c d f := by
        ext ψ
        change CartesianMonoidalCategory.toUnit (k.obj d.unop) ≫ v =
          k.map f.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop) ≫ v
        have hu : k.map f.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop) =
            CartesianMonoidalCategory.toUnit (k.obj d.unop) :=
          CartesianMonoidalCategory.toUnit_unique _ _
        calc
          _ = (k.map f.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop)) ≫ v :=
            (congrArg (fun q => q ≫ v) hu).symm
          _ = _ := by cat_disch }
  exact CartesianMonoidalCategory.lift ν (𝟙 _)

theorem restrictionDeformationSection_comp_snd {C : Type u} [SmallCategory C]
    {k k' : C ⥤ SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ Δ[1]) (X : SSet.{u}) :
    restrictionDeformationSection (k := k) (k' := k') v X ≫
      CartesianMonoidalCategory.snd _ _ = 𝟙 ((simplicialRestriction k').obj X) := by
  unfold restrictionDeformationSection
  simp only [CartesianMonoidalCategory.lift_snd]

theorem restrictionDeformationSection_comp_homotopy {C : Type u} [SmallCategory C]
    {k k' : C ⥤ SSet.{u}} (π : k' ⟶ k)
    (H : k' ⋙ tensorLeft Δ[1] ⟶ k') (v : 𝟙_ SSet.{u} ⟶ Δ[1])
    (ε : k' ⟶ k') (hv : ∀ c, CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit (k'.obj c) ≫ v) (𝟙 _) ≫ H.app c = ε.app c)
    (X : SSet.{u}) :
    restrictionDeformationSection (k := k) (k' := k') v X ≫
      restrictionDeformationHomotopy π H X =
        (simplicialRestrictionMap ε).app X := by
  ext c ψ
  change (CartesianMonoidalCategory.lift
      (π.app c.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop) ≫ v)
      (𝟙 _) ≫ H.app c.unop ≫ ψ) = ε.app c.unop ≫ ψ
  have hu : π.app c.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop) =
      CartesianMonoidalCategory.toUnit (k'.obj c.unop) :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have hc : π.app c.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop) ≫ v =
      CartesianMonoidalCategory.toUnit (k'.obj c.unop) ≫ v := by
    calc
      _ = (π.app c.unop ≫ CartesianMonoidalCategory.toUnit (k.obj c.unop)) ≫ v := by
        cat_disch
      _ = _ := congrArg (fun q => q ≫ v) hu
  rw [hc]
  exact congrArg (fun q => q ≫ ψ) (hv c.unop)

namespace BasicLocalizer

theorem wPsh_simplicialRestrictionMap_of_deformation {C : Type u} [SmallCategory C]
    (𝒲 : BasicLocalizer.{u}) {k k' : C ⥤ SSet.{u}} (π : k' ⟶ k) (σ : k ⟶ k')
    (hσ : σ ≫ π = 𝟙 k) (v₀ v₁ : 𝟙_ SSet.{u} ⟶ Δ[1])
    (H : k' ⋙ tensorLeft Δ[1] ⟶ k')
    (h₀ : ∀ c, CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit (k'.obj c) ≫ v₀) (𝟙 _) ≫ H.app c =
        (π ≫ σ).app c)
    (h₁ : ∀ c, CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit (k'.obj c) ≫ v₁) (𝟙 _) ≫ H.app c =
        (𝟙 k' : k' ⟶ k').app c)
    (hJ : 𝒲.LocallyAspherical C ((simplicialRestriction k).obj Δ[1]))
    (X : SSet.{u}) : 𝒲.wPsh C ((simplicialRestrictionMap π).app X) := by
  let s := (simplicialRestrictionMap π).app X
  let r := (simplicialRestrictionMap σ).app X
  have hsr : s ≫ r = 𝟙 ((simplicialRestriction k).obj X) := by
    ext c ψ
    change σ.app c.unop ≫ π.app c.unop ≫ ψ = ψ
    have hc := congrArg (fun θ : k ⟶ k => θ.app c.unop) hσ
    change σ.app c.unop ≫ π.app c.unop = 𝟙 _ at hc
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ ψ) hc).trans (Category.id_comp _))
  have hrs : r ≫ s = (simplicialRestrictionMap (π ≫ σ)).app X := by
    ext c ψ
    rfl
  let i₀ := restrictionDeformationSection (k := k) (k' := k') v₀ X
  let i₁ := restrictionDeformationSection (k := k) (k' := k') v₁ X
  let hh := restrictionDeformationHomotopy π H X
  have he₀ : i₀ ≫ hh = r ≫ s := by
    rw [hrs]
    exact restrictionDeformationSection_comp_homotopy π H v₀ (π ≫ σ) h₀ X
  have he₁ : i₁ ≫ hh = 𝟙 ((simplicialRestriction k').obj X) := by
    rw [restrictionDeformationSection_comp_homotopy π H v₁ (𝟙 k') h₁ X]
    ext c ψ
    rfl
  have hw : 𝒲.wPsh C (r ≫ s) :=
    𝒲.wPsh_of_homotopic_id hJ i₀ i₁
      (restrictionDeformationSection_comp_snd v₀ X)
      (restrictionDeformationSection_comp_snd v₁ X) hh (r ≫ s) he₀ he₁
  exact 𝒲.wPsh_of_retraction s r hsr hw

end BasicLocalizer

def rightFactorSection {C : Type u} [SmallCategory C]
    (k : C ⥤ SSet.{u}) {T : SSet.{u}} (c : SimplicialContraction T) :
    k ⟶ k ⋙ tensorRight T where
  app a := CartesianMonoidalCategory.lift (𝟙 _) (CartesianMonoidalCategory.toUnit _ ≫ c.pt)
  naturality a b f := by
    apply CartesianMonoidalCategory.hom_ext
    · cat_disch
    · cat_disch

def rightFactorHomotopy {C : Type u} [SmallCategory C]
    (k : C ⥤ SSet.{u}) {T : SSet.{u}} (c : SimplicialContraction T) :
    (k ⋙ tensorRight T) ⋙ tensorLeft Δ[1] ⟶ k ⋙ tensorRight T where
  app a := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.fst _ _)
    ((𝟙 Δ[1] ⊗ₘ CartesianMonoidalCategory.snd _ _) ≫ c.homotopy)
  naturality a b f := by
    apply CartesianMonoidalCategory.hom_ext
    · cat_disch
    · cat_disch

namespace BasicLocalizer

theorem wPsh_rightFactorProjection {C : Type u} [SmallCategory C]
    (𝒲 : BasicLocalizer.{u}) (k : C ⥤ SSet.{u}) {T : SSet.{u}}
    (c : SimplicialContraction T)
    (hJ : 𝒲.LocallyAspherical C ((simplicialRestriction k).obj Δ[1]))
    (X : SSet.{u}) :
    𝒲.wPsh C ((simplicialRestrictionMap (SSet.rightFactorProjection k T)).app X) := by
  let π := SSet.rightFactorProjection k T
  let σ := rightFactorSection k c
  let H := rightFactorHomotopy k c
  have hσ : σ ≫ π = 𝟙 k := by
    ext a n x
    rfl
  have h0 : ∀ a, CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit ((k ⋙ tensorRight T).obj a) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1))
      (𝟙 _) ≫ H.app a = (π ≫ σ).app a := by
    intro a
    ext n p
    apply Prod.ext
    · rfl
    · change ((CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (𝟙 T) ≫
            c.homotopy).app n p.2) =
          ((CartesianMonoidalCategory.toUnit T ≫ c.pt).app n p.2)
      exact congrArg (fun g : T ⟶ T => g.app n p.2) c.homotopy_one
  have h1 : ∀ a, CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.toUnit ((k ⋙ tensorRight T).obj a) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))
      (𝟙 _) ≫ H.app a = (𝟙 (k ⋙ tensorRight T) : _).app a := by
    intro a
    ext n p
    apply Prod.ext
    · rfl
    · change ((CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit T ≫
              SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) (𝟙 T) ≫
            c.homotopy).app n p.2) = ((𝟙 T : T ⟶ T).app n p.2)
      exact congrArg (fun g : T ⟶ T => g.app n p.2) c.homotopy_zero
  exact 𝒲.wPsh_simplicialRestrictionMap_of_deformation π σ hσ
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))
    H h0 h1 hJ X

theorem wPsh_simplicialRestrictionMap_iso_comp {C : Type u} [SmallCategory C]
    (𝒲 : BasicLocalizer.{u}) {k k' k'' : C ⥤ SSet.{u}} (e : k'' ≅ k') (π : k' ⟶ k)
    (X : SSet.{u}) (h : 𝒲.wPsh C ((simplicialRestrictionMap π).app X)) :
    𝒲.wPsh C ((simplicialRestrictionMap (e.hom ≫ π)).app X) :=
  (𝒲.wPsh C).comp_mem _ _ h (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _
    ((Functor.isoWhiskerLeft yoneda
      ((Functor.whiskeringLeft Cᵒᵖ SSet.{u}ᵒᵖ (Type u)).mapIso (NatIso.op e))).app X).isIso_hom)

end BasicLocalizer

end Bisimplicial

section BisimplicialFibres

open MonoidalCategory

namespace BasicLocalizer

theorem wPsh_bisimplicialShapeFst (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A] (X : SSet.{u}) :
    𝒲.wPsh (A × (AsSmall.{u} SimplexCategory))
      ((simplicialRestrictionMap (bisimplicialShapeFst A)).app X) := by
  refine 𝒲.wPsh_prod_of_forall_sectL _ fun b => ?_
  let i := Prod.sectL A b
  let k := i ⋙ CategoryTheory.Prod.fst A (AsSmall.{u} SimplexCategory) ⋙
    Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor
  let T := Δ[(ULift.down b).len]
  let e : i ⋙ bisimplicialShape A ≅ k ⋙ tensorRight T :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun {c d} f => by
      have hmap : (bisimplicialShape A).map (i.map f) = k.map f ▷ T := by
        change (k.map f ⊗ₘ SSet.stdSimplex.map (𝟙 (ULift.down b))) = _
        exact (congrArg (k.map f ⊗ₘ ·) (SSet.stdSimplex.map_id _)).trans
          (MonoidalCategory.tensorHom_id _ _)
      simp only [Functor.comp_map]
      rw [hmap]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hπ : Functor.whiskerLeft i (bisimplicialShapeFst A) =
      e.hom ≫ SSet.rightFactorProjection k T := by
    ext c : 2
    exact (Category.id_comp _).symm
  change 𝒲.wPsh _
    ((simplicialRestrictionMap (Functor.whiskerLeft i (bisimplicialShapeFst A))).app X)
  rw [hπ]
  exact 𝒲.wPsh_simplicialRestrictionMap_iso_comp e _ X
    (𝒲.wPsh_rightFactorProjection k (stdSimplexContraction (ULift.down b).len)
      (𝒲.locallyAspherical_rightAdjoint_interval A) X)

theorem wPsh_bisimplicialShapeSnd (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    (X : SSet.{u}) :
    𝒲.wPsh (A × (AsSmall.{u} SimplexCategory))
      ((simplicialRestrictionMap (bisimplicialShapeSnd A)).app X) := by
  refine 𝒲.wPsh_prod_of_forall_sectR _ fun a => ?_
  let i := Prod.sectR a (AsSmall.{u} SimplexCategory)
  let k := i ⋙ CategoryTheory.Prod.snd A (AsSmall.{u} SimplexCategory) ⋙
    AsSmall.down ⋙ SSet.stdSimplex
  let T := CategoryTheory.nerve (Over a)
  let e : i ⋙ bisimplicialShape A ≅ k ⋙ tensorRight T :=
    NatIso.ofComponents (fun _ => β_ _ _) (fun {b d} f => by
      have hmap : (bisimplicialShape A).map (i.map f) = (𝟙 T ⊗ₘ SSet.stdSimplex.map f.down) := by
        change (CategoryTheory.nerveFunctor.map ((Over.mapFunctor A).map (𝟙 a)) ⊗ₘ
          SSet.stdSimplex.map f.down) = _
        rw [(Over.mapFunctor A).map_id a,
          CategoryTheory.nerveFunctor.map_id ((Over.mapFunctor A).obj a)]
        rfl
      simp only [Functor.comp_map]
      rw [hmap]
      exact BraidedCategory.braiding_naturality _ _)
  have hπ : Functor.whiskerLeft i (bisimplicialShapeSnd A) =
      e.hom ≫ SSet.rightFactorProjection k T := by
    ext b : 2
    exact (CartesianMonoidalCategory.braiding_hom_fst _ _).symm
  change 𝒲.wPsh _
    ((simplicialRestrictionMap (Functor.whiskerLeft i (bisimplicialShapeSnd A))).app X)
  rw [hπ]
  exact 𝒲.wPsh_simplicialRestrictionMap_iso_comp e _ X
    (𝒲.wPsh_rightFactorProjection k (overNerveContraction a)
      𝒲.locallyAspherical_restriction_stdSimplex X)

end BasicLocalizer

end BisimplicialFibres

namespace BasicLocalizer

theorem ordinaryNerveElementsRightAdjoint_map_mem
    (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A]
    {K L : SSet.{u}} (f : K ⟶ L) (hf : 𝒲.wSSet f) :
    𝒲.wPsh A ((ordinaryNerveElementsRightAdjoint A).map f) := by
  let kP := CategoryTheory.Prod.fst A (AsSmall.{u} SimplexCategory) ⋙
    Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor
  let kJ := bisimplicialShape A
  let kQ := CategoryTheory.Prod.snd A (AsSmall.{u} SimplexCategory) ⋙ AsSmall.down ⋙
    SSet.stdSimplex
  let P := simplicialRestriction kP
  let J := simplicialRestriction kJ
  let Q := simplicialRestriction kQ
  let θP := simplicialRestrictionMap (bisimplicialShapeFst A)
  let θQ := simplicialRestrictionMap (bisimplicialShapeSnd A)
  let V := 𝒲.wPsh (A × (AsSmall.{u} SimplexCategory))
  have hQ : V (Q.map f) := by
    apply 𝒲.wPsh_prod_of_forall_sectR _
    intro a
    exact (𝒲.wPsh_simplicialRestriction_stdSimplex_map_iff f).2 hf
  have hJ : V (J.map f) := by
    apply V.of_precomp _ _ (𝒲.wPsh_bisimplicialShapeSnd A K)
    rw [← θQ.naturality f]
    exact V.comp_mem _ _ hQ (𝒲.wPsh_bisimplicialShapeSnd A L)
  have hP : V (P.map f) := by
    apply V.of_postcomp _ _ (𝒲.wPsh_bisimplicialShapeFst A L)
    rw [θP.naturality f]
    exact V.comp_mem _ _ (𝒲.wPsh_bisimplicialShapeFst A K) hJ
  exact 𝒲.wPsh_of_wPsh_whiskerLeft_fst (AsSmall.up.obj ⦋0⦌ : (AsSmall.{u} SimplexCategory))
    ((ordinaryNerveElementsRightAdjoint A).map f) hP

end BasicLocalizer

section ProductSlice

variable {A : Type u} [SmallCategory A] (X : Aᵒᵖ ⥤ Type u)

def rightAdjointSliceComponentEquiv (K : SSet.{u}) (e : CostructuredArrow yoneda X) :
    (((ordinaryNerveElementsRightAdjoint (CostructuredArrow yoneda X)).obj K).obj (op e)) ≃
      (((ordinaryNerveElementsRightAdjoint A).obj K).obj (op e.left)) :=
  (CategoryTheory.nerveFunctor.mapIso (CostructuredArrow.sliceIso X e)).homFromEquiv

def rightAdjointSliceIso (K : SSet.{u}) :
    (ordinaryNerveElementsRightAdjoint (CostructuredArrow yoneda X)).obj K ≅
      (CostructuredArrow.proj yoneda X).op ⋙
        (ordinaryNerveElementsRightAdjoint A).obj K :=
  NatIso.ofComponents
    (fun e => (rightAdjointSliceComponentEquiv X K e.unop).toIso)
    (by
      intro e e' g
      ext h
      change CategoryTheory.nerveFunctor.obj (Cat.of (Over e.unop)) ⟶ K at h
      change (CategoryTheory.nerveFunctor.mapIso (CostructuredArrow.sliceIso X e'.unop)).inv ≫
          CategoryTheory.nerveFunctor.map ((Over.map g.unop).toCatHom) ≫ h =
        CategoryTheory.nerveFunctor.map ((Over.map g.unop.left).toCatHom) ≫
          (CategoryTheory.nerveFunctor.mapIso (CostructuredArrow.sliceIso X e.unop)).inv ≫ h
      let i₀ := CategoryTheory.nerveFunctor.mapIso (CostructuredArrow.sliceIso X e'.unop)
      let i₁ := CategoryTheory.nerveFunctor.mapIso (CostructuredArrow.sliceIso X e.unop)
      let p := CategoryTheory.nerveFunctor.map ((Over.map g.unop).toCatHom)
      let q := CategoryTheory.nerveFunctor.map ((Over.map g.unop.left).toCatHom)
      have hn : i₀.hom ≫ q = p ≫ i₁.hom := by
        change CategoryTheory.nerveFunctor.map (CostructuredArrow.sliceIso X e'.unop).hom ≫
          CategoryTheory.nerveFunctor.map ((Over.map g.unop.left).toCatHom) =
          CategoryTheory.nerveFunctor.map ((Over.map g.unop).toCatHom) ≫
            CategoryTheory.nerveFunctor.map (CostructuredArrow.sliceIso X e.unop).hom
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      have hn' : i₀.inv ≫ p = q ≫ i₁.inv := by
        calc
          i₀.inv ≫ p = i₀.inv ≫ (p ≫ i₁.hom) ≫ i₁.inv := by simp [Category.assoc]
          _ = i₀.inv ≫ (i₀.hom ≫ q) ≫ i₁.inv := by rw [hn]
          _ = q ≫ i₁.inv := by simp [Category.assoc]
      change (i₀.inv ≫ p) ≫ h = (q ≫ i₁.inv) ≫ h
      rw [hn'])

def rightAdjointSliceNatIso :
    ordinaryNerveElementsRightAdjoint (CostructuredArrow yoneda X) ≅
      ordinaryNerveElementsRightAdjoint A ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj (CostructuredArrow.proj yoneda X).op :=
  NatIso.ofComponents (rightAdjointSliceIso X) (by
    intro K L f
    ext e h
    rfl)

noncomputable def sliceForgetRestrictionNatIso :
    (Functor.whiskeringLeft _ _ (Type u)).obj (CostructuredArrow.proj yoneda X).op ⋙
        sliceForget X ≅ Over.star X ⋙ Over.forget X :=
  let E := overEquivPresheafCostructuredArrow X
  Functor.isoWhiskerRight (sliceStarIso X).symm (sliceForget X) ≪≫
    Functor.associator (Over.star X) E.functor (sliceForget X) ≪≫
      Functor.isoWhiskerLeft (Over.star X)
        (Functor.associator E.functor E.inverse (Over.forget X)).symm ≪≫
        (Functor.associator (Over.star X) (E.functor ⋙ E.inverse) (Over.forget X)).symm ≪≫
          Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Over.star X) E.unitIso.symm)
            (Over.forget X) ≪≫
            Functor.isoWhiskerRight (Functor.rightUnitor (Over.star X)) (Over.forget X)

noncomputable def rightAdjointProductIso :
    ordinaryNerveElementsRightAdjoint (CostructuredArrow yoneda X) ⋙ sliceForget X ≅
      ordinaryNerveElementsRightAdjoint A ⋙ (Over.star X ⋙ Over.forget X) :=
  Functor.isoWhiskerRight (rightAdjointSliceNatIso X) (sliceForget X) ≪≫
    Functor.associator (ordinaryNerveElementsRightAdjoint A)
      ((Functor.whiskeringLeft _ _ (Type u)).obj (CostructuredArrow.proj yoneda X).op)
        (sliceForget X) ≪≫
      Functor.isoWhiskerLeft (ordinaryNerveElementsRightAdjoint A)
        (sliceForgetRestrictionNatIso X)

end ProductSlice

namespace BasicLocalizer

theorem prod_rightAdjoint_map_mem (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A]
    (X : Aᵒᵖ ⥤ Type u) {K L : SSet.{u}} (f : K ⟶ L)
    (hf : 𝒲.wSSet f) :
    𝒲.wPsh A (Limits.prod.map (𝟙 X) ((ordinaryNerveElementsRightAdjoint A).map f)) := by
  have hRf := 𝒲.ordinaryNerveElementsRightAdjoint_map_mem (CostructuredArrow yoneda X) f hf
  rw [𝒲.wPsh_costructuredArrow_eq X] at hRf
  exact ((𝒲.wPsh A).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (rightAdjointProductIso X) (Arrow.mk f))).1 hRf

end BasicLocalizer

end Atoms.TestCategory
