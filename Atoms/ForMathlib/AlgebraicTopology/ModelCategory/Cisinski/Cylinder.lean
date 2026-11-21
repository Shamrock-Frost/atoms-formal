import Atoms.ForMathlib.CategoryTheory.Adhesive.Basic
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Types.Pushouts

open CategoryTheory Limits

namespace HomotopicalAlgebra

structure ExactCylinder.{w, v, u} (C : Type u) [Category.{v} C] [HasBinaryCoproducts C] where
  I : C ⥤ C
  endpoint : Bool → (𝟭 C ⟶ I)
  contraction : I ⟶ 𝟭 C
  endpoint_contraction : ∀ ε : Bool, endpoint ε ≫ contraction = 𝟙 _
  mono_endpoints : ∀ X : C,
    Mono (coprod.desc ((endpoint false).app X) ((endpoint true).app X))
  [preservesMonomorphisms : I.PreservesMonomorphisms]
  [preservesColimits : PreservesColimitsOfSize.{w, w} I]

attribute [instance] ExactCylinder.preservesMonomorphisms ExactCylinder.preservesColimits

universe w v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

instance (𝕀 : ExactCylinder.{w} C) : PreservesColimitsOfSize.{0, 0} 𝕀.I :=
  preservesColimitsOfSize_shrink _

namespace ExactCylinder

variable (𝕀 : ExactCylinder.{w} C)

theorem endpoint_naturality (ε : Bool) {K X : C} (i : K ⟶ X) :
    (𝕀.endpoint ε).app K ≫ 𝕀.I.map i = i ≫ (𝕀.endpoint ε).app X :=
  ((𝕀.endpoint ε).naturality i).symm

theorem endpoint_naturality_assoc (ε : Bool) {K X Z : C} (i : K ⟶ X)
    (h : 𝕀.I.obj X ⟶ Z) :
    (𝕀.endpoint ε).app K ≫ 𝕀.I.map i ≫ h = i ≫ (𝕀.endpoint ε).app X ≫ h := by
  rw [← Category.assoc, 𝕀.endpoint_naturality, Category.assoc]

@[simp]
theorem endpoint_app_contraction_app (ε : Bool) (X : C) :
    (𝕀.endpoint ε).app X ≫ (𝕀.contraction).app X = 𝟙 X := by
  rw [← NatTrans.comp_app, 𝕀.endpoint_contraction ε]
  rfl

@[simp]
theorem endpoint_app_contraction_app_assoc (ε : Bool) {X Z : C} (h : X ⟶ Z) :
    (𝕀.endpoint ε).app X ≫ (𝕀.contraction).app X ≫ h = h := by
  rw [← Category.assoc, 𝕀.endpoint_app_contraction_app]
  exact Category.id_comp h

theorem map_contraction_app {X Y : C} (f : X ⟶ Y) :
    𝕀.I.map f ≫ (𝕀.contraction).app Y = (𝕀.contraction).app X ≫ f :=
  (𝕀.contraction).naturality f

theorem map_contraction_app_assoc {X Y Z : C} (f : X ⟶ Y) (h : Y ⟶ Z) :
    𝕀.I.map f ≫ (𝕀.contraction).app Y ≫ h = (𝕀.contraction).app X ≫ f ≫ h := by
  rw [← Category.assoc, 𝕀.map_contraction_app, Category.assoc]

structure DeformationRetract {K L : C} (i : K ⟶ L) where
  retraction : L ⟶ K
  homotopy : 𝕀.I.obj L ⟶ L
  comp_retraction : i ≫ retraction = 𝟙 K
  endpoint_false_comp_homotopy : (𝕀.endpoint false).app L ≫ homotopy = 𝟙 L
  endpoint_true_comp_homotopy : (𝕀.endpoint true).app L ≫ homotopy = retraction ≫ i
  map_comp_homotopy : 𝕀.I.map i ≫ homotopy = 𝕀.I.map i ≫ 𝕀.contraction.app L

theorem isPullback_endpoint (ε : Bool) {K X : C} (i : K ⟶ X) [Mono i] :
    IsPullback ((𝕀.endpoint ε).app K) i (𝕀.I.map i) ((𝕀.endpoint ε).app X) :=
  isPullback_app_of_retraction 𝕀.I (𝕀.endpoint ε) 𝕀.contraction (𝕀.endpoint_contraction ε) i

noncomputable def endpoints (X : C) : X ⨿ X ⟶ 𝕀.I.obj X :=
  coprod.desc ((𝕀.endpoint false).app X) ((𝕀.endpoint true).app X)

instance (X : C) : Mono (𝕀.endpoints X) := 𝕀.mono_endpoints X

theorem endpoints_naturality {K X : C} (i : K ⟶ X) :
    𝕀.endpoints K ≫ 𝕀.I.map i = coprod.map i i ≫ 𝕀.endpoints X := by
  refine coprod.hom_ext ?_ ?_ <;>
    simp [endpoints, endpoint_naturality]

@[reassoc]
theorem inl_endpoints (K : C) :
    coprod.inl ≫ 𝕀.endpoints K = (𝕀.endpoint false).app K :=
  coprod.inl_desc _ _

@[reassoc]
theorem inr_endpoints (K : C) :
    coprod.inr ≫ 𝕀.endpoints K = (𝕀.endpoint true).app K :=
  coprod.inr_desc _ _

theorem exists_map_coprod_comp (X : C) :
    ∃ ψ : 𝕀.I.obj (X ⨿ X) ⟶ 𝕀.I.obj X ⨿ 𝕀.I.obj X,
      𝕀.I.map coprod.inl ≫ ψ = coprod.inl ∧ 𝕀.I.map coprod.inr ≫ ψ = coprod.inr :=
  ⟨_, map_inl_inv_coprodComparison 𝕀.I, map_inr_inv_coprodComparison 𝕀.I⟩

theorem mono_endpoint (ε : Bool) (X : C) : Mono ((𝕀.endpoint ε).app X) :=
  SplitMono.mono ⟨(𝕀.contraction).app X, 𝕀.endpoint_app_contraction_app ε X⟩

theorem isPullback_endpoints [HasPullbacks C] [FinitaryPreExtensive C] {K X : C} (i : K ⟶ X)
    (hi : Mono i) :
    IsPullback (𝕀.endpoints K) (coprod.map i i) (𝕀.I.map i) (𝕀.endpoints X) := by
  have hau : IsUniversalColimit (colimit.cocone (pair X X)) :=
    FinitaryPreExtensive.universal' _ (colimit.isColimit _)
  let f : ∀ j : WalkingPair, (pairFunction X X) j ⟶ 𝕀.I.obj X := fun j =>
    WalkingPair.casesOn j ((𝕀.endpoint false).app X) ((𝕀.endpoint true).app X)
  let q₁ : ∀ j : WalkingPair, (pairFunction K K) j ⟶ 𝕀.I.obj K := fun j =>
    WalkingPair.casesOn j ((𝕀.endpoint false).app K) ((𝕀.endpoint true).app K)
  let q₂ : ∀ j : WalkingPair, (pairFunction K K) j ⟶ (pairFunction X X) j := fun j =>
    WalkingPair.casesOn j i i
  have h := hau.isPullback_of_isColimit_left f (𝕀.endpoints X) (𝕀.I.map i) q₁ q₂
    (fun j => by cases j <;> exact 𝕀.isPullback_endpoint _ i) (colimit.isColimit (pair K K))
    (by rintro (_ | _); exacts [coprod.inl_desc _ _, coprod.inr_desc _ _])
  have e₁ : Cofan.IsColimit.desc (colimit.isColimit (pair K K)) q₁ = 𝕀.endpoints K :=
    coprod.hom_ext (((colimit.isColimit (pair K K)).fac _ _).trans (coprod.inl_desc _ _).symm)
      (((colimit.isColimit (pair K K)).fac _ _).trans (coprod.inr_desc _ _).symm)
  have e₂ : Cofan.IsColimit.desc (colimit.isColimit (pair K K))
      (fun j => q₂ j ≫ Cofan.inj (colimit.cocone (pair X X)) j) = coprod.map i i :=
    coprod.hom_ext (((colimit.isColimit (pair K K)).fac _ _).trans (coprod.inl_map i i).symm)
      (((colimit.isColimit (pair K K)).fac _ _).trans (coprod.inr_map i i).symm)
  exact e₁ ▸ e₂ ▸ h

variable [HasPushouts C]

noncomputable def endpointBoxSource (ε : Bool) {K X : C} (i : K ⟶ X) :
    C :=
  pushout ((𝕀.endpoint ε).app K) i

noncomputable def endpointBox (ε : Bool) {K X : C} (i : K ⟶ X) :
    𝕀.endpointBoxSource ε i ⟶ 𝕀.I.obj X :=
  pushout.desc (𝕀.I.map i) ((𝕀.endpoint ε).app X) (𝕀.endpoint_naturality ε i)

theorem inl_endpointBox (ε : Bool) {K X : C} (i : K ⟶ X) :
    pushout.inl _ _ ≫ 𝕀.endpointBox ε i = 𝕀.I.map i :=
  pushout.inl_desc _ _ _

theorem inl_endpointBox_assoc (ε : Bool) {K X Z : C} (i : K ⟶ X)
    (h : 𝕀.I.obj X ⟶ Z) : pushout.inl _ _ ≫ 𝕀.endpointBox ε i ≫ h = 𝕀.I.map i ≫ h :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) (𝕀.inl_endpointBox ε i))

theorem inr_endpointBox (ε : Bool) {K X : C} (i : K ⟶ X) :
    pushout.inr _ _ ≫ 𝕀.endpointBox ε i = (𝕀.endpoint ε).app X :=
  pushout.inr_desc _ _ _

theorem inr_endpointBox_assoc (ε : Bool) {K X Z : C} (i : K ⟶ X)
    (h : 𝕀.I.obj X ⟶ Z) :
    pushout.inr _ _ ≫ 𝕀.endpointBox ε i ≫ h = (𝕀.endpoint ε).app X ≫ h :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) (𝕀.inr_endpointBox ε i))

noncomputable abbrev bothBoxSource {K X : C} (i : K ⟶ X) : C :=
  pushout (𝕀.endpoints K) (coprod.map i i)

noncomputable def bothBox {K X : C} (i : K ⟶ X) :
    𝕀.bothBoxSource i ⟶ 𝕀.I.obj X :=
  pushout.desc (𝕀.I.map i) (𝕀.endpoints X) (𝕀.endpoints_naturality i)

@[reassoc]
theorem inl_bothBox {K X : C} (i : K ⟶ X) :
    pushout.inl _ _ ≫ 𝕀.bothBox i = 𝕀.I.map i :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem inr_bothBox {K X : C} (i : K ⟶ X) :
    pushout.inr _ _ ≫ 𝕀.bothBox i = 𝕀.endpoints X :=
  pushout.inr_desc _ _ _

theorem map_comp_eq_of_endpointBox_comp_eq (ε : Bool) {K X Z : C} (i : K ⟶ X)
    {H : 𝕀.I.obj X ⟶ Z} {a : 𝕀.I.obj K ⟶ Z} {b : X ⟶ Z}
    {w : (𝕀.endpoint ε).app K ≫ a = i ≫ b}
    (h : 𝕀.endpointBox ε i ≫ H = pushout.desc a b w) : 𝕀.I.map i ≫ H = a :=
  (𝕀.inl_endpointBox_assoc ε i H).symm.trans
    ((congrArg (pushout.inl _ _ ≫ ·) h).trans (pushout.inl_desc _ _ _))

theorem endpoint_comp_eq_of_endpointBox_comp_eq (ε : Bool) {K X Z : C} (i : K ⟶ X)
    {H : 𝕀.I.obj X ⟶ Z} {a : 𝕀.I.obj K ⟶ Z} {b : X ⟶ Z}
    {w : (𝕀.endpoint ε).app K ≫ a = i ≫ b}
    (h : 𝕀.endpointBox ε i ≫ H = pushout.desc a b w) : (𝕀.endpoint ε).app X ≫ H = b :=
  (𝕀.inr_endpointBox_assoc ε i H).symm.trans
    ((congrArg (pushout.inr _ _ ≫ ·) h).trans (pushout.inr_desc _ _ _))

theorem map_comp_eq_of_bothBox_comp_eq {K X Z : C} (i : K ⟶ X)
    {H : 𝕀.I.obj X ⟶ Z} {a : 𝕀.I.obj K ⟶ Z} {b : X ⨿ X ⟶ Z}
    {w : 𝕀.endpoints K ≫ a = coprod.map i i ≫ b}
    (h : 𝕀.bothBox i ≫ H = pushout.desc a b w) : 𝕀.I.map i ≫ H = a :=
  (𝕀.inl_bothBox_assoc i H).symm.trans
    ((congrArg (pushout.inl _ _ ≫ ·) h).trans (pushout.inl_desc _ _ _))

theorem endpoints_comp_eq_of_bothBox_comp_eq {K X Z : C} (i : K ⟶ X)
    {H : 𝕀.I.obj X ⟶ Z} {a : 𝕀.I.obj K ⟶ Z} {b : X ⨿ X ⟶ Z}
    {w : 𝕀.endpoints K ≫ a = coprod.map i i ≫ b}
    (h : 𝕀.bothBox i ≫ H = pushout.desc a b w) : 𝕀.endpoints X ≫ H = b :=
  (𝕀.inr_bothBox_assoc i H).symm.trans
    ((congrArg (pushout.inr _ _ ≫ ·) h).trans (pushout.inr_desc _ _ _))

theorem mono_endpointBox [HasEffectiveUnions C] (ε : Bool) {K X : C} (i : K ⟶ X)
    (hi : Mono i) :
    Mono (𝕀.endpointBox ε i) := by
  have := hi
  have := 𝕀.mono_endpoint ε X
  exact HasEffectiveUnions.mono_pushoutDesc (𝕀.isPullback_endpoint ε i)

theorem mono_bothBox [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] {K X : C}
    (i : K ⟶ X) (hi : Mono i) : Mono (𝕀.bothBox i) := by
  have := hi
  exact HasEffectiveUnions.mono_pushoutDesc (𝕀.isPullback_endpoints i hi)

noncomputable def endpointRetractArrow [HasInitial C] (ε : Bool) (Y : C) :
    RetractArrow ((𝕀.endpoint ε).app Y) (𝕀.endpointBox ε (initial.to Y)) :=
  haveI hI : IsInitial (𝕀.I.obj (⊥_ (C))) := initialIsInitial.isInitialObj 𝕀.I _
  let r : 𝕀.endpointBoxSource ε (initial.to Y) ⟶ Y :=
    pushout.desc (hI.to Y) (𝟙 Y) (initial.hom_ext _ _)
  have hinr : (pushout.inr _ _ : Y ⟶ 𝕀.endpointBoxSource ε (initial.to Y)) ≫
      𝕀.endpointBox ε (initial.to Y) = (𝕀.endpoint ε).app Y := pushout.inr_desc _ _ _
  have hri : (pushout.inr _ _ : Y ⟶ 𝕀.endpointBoxSource ε (initial.to Y)) ≫ r = 𝟙 Y :=
    pushout.inr_desc _ _ _
  { i := Arrow.homMk (pushout.inr _ _ : Y ⟶ 𝕀.endpointBoxSource ε (initial.to Y)) (𝟙 _)
      (by rw [Category.comp_id]; exact hinr)
    r := Arrow.homMk r (𝟙 _) (by
      rw [Category.comp_id]
      refine pushout.hom_ext (hI.hom_ext _ _) ?_
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (𝕀.endpoint ε).app Y) hri).trans (Category.id_comp _))).trans
          hinr.symm)
    retract := by
      apply Arrow.hom_ext
      · exact hri
      · exact Category.comp_id _ }

end ExactCylinder

variable (C) in
def CylinderCompatibleWith (V : MorphismProperty C) (𝕀 : ExactCylinder.{w} C) : Prop :=
  ∀ X : C, V (𝕀.contraction.app X)

end HomotopicalAlgebra
