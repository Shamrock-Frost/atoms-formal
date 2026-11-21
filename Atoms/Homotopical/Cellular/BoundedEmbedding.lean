import Atoms.Homotopical.Cellular.BoundedPresheaf
import Atoms.Homotopical.Cellular.Model
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Colimits
import Atoms.ForMathlib.CategoryTheory.Sites.Separated
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Image

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe w v u

structure BoundedEmbedding (C : Type u) [Category.{v} C] (B : Type v) [SmallCategory B] where
  ι : C ⥤ Bᵒᵖ ⥤ Type v
  fullyFaithful : ι.FullyFaithful
  [isAccessible : ι.IsAccessible.{v}]
  [preservesMonomorphisms : ι.PreservesMonomorphisms]
  sub {X : C} (S : Subfunctor (ι.obj X)) : C
  subIso {X : C} (S : Subfunctor (ι.obj X)) : ι.obj (sub S) ≅ S.toFunctor

namespace BoundedEmbedding

variable {C : Type u} [Category.{v} C] {B : Type v} [SmallCategory B] (E : BoundedEmbedding C B)

attribute [instance] isAccessible preservesMonomorphisms

def id (B : Type v) [SmallCategory B] : BoundedEmbedding (Bᵒᵖ ⥤ Type v) B where
  ι := 𝟭 _
  fullyFaithful := Functor.FullyFaithful.id _
  isAccessible := ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  preservesMonomorphisms := inferInstance
  sub S := S.toFunctor
  subIso _ := Iso.refl _

def asSmall (A : Type v) [SmallCategory A] :
    BoundedEmbedding (Aᵒᵖ ⥤ Type (max w v)) (AsSmall.{max w v} A) where
  ι := ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft).functor
  fullyFaithful := ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft).fullyFaithfulFunctor
  isAccessible := ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  preservesMonomorphisms := inferInstance
  sub S := ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft).inverse.obj S.toFunctor
  subIso S := ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft).counitIso.app S.toFunctor

def separated (J : GrothendieckTopology B) :
    BoundedEmbedding (SeparatedPresheaf.{max w v} J) (AsSmall.{max w v} B) where
  ι := ObjectProperty.ι _ ⋙ ((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).functor
  fullyFaithful := (ObjectProperty.fullyFaithfulι _).comp
    ((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).fullyFaithfulFunctor
  isAccessible := by
    obtain ⟨κ, hκ, hB⟩ := HasCardinalLT.exists_regular_cardinal.{max w v} (Arrow B)
    have : Fact κ.IsRegular := ⟨hκ⟩
    have := SeparatedPresheaf.isCardinalAccessible_ι J κ hB
    exact Functor.isAccessible_of_isCardinalAccessible _ κ
  preservesMonomorphisms := inferInstance
  sub {X} S := ⟨((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).inverse.obj S.toFunctor,
    fun _ T hT => (X.2 T hT).of_mono
      (((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).inverse.map S.ι ≫
        ((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).unitIso.inv.app X.obj)⟩
  subIso S :=
    ((AsSmall.equiv : B ≌ AsSmall.{max w v} B).op.congrLeft).counitIso.app S.toFunctor

variable {X : C}

def subι (S : Subfunctor (E.ι.obj X)) : E.sub S ⟶ X :=
  E.fullyFaithful.preimage ((E.subIso S).hom ≫ S.ι)

@[simp]
theorem map_subι (S : Subfunctor (E.ι.obj X)) : E.ι.map (E.subι S) = (E.subIso S).hom ≫ S.ι :=
  E.fullyFaithful.map_preimage _

instance mono_map_subι (S : Subfunctor (E.ι.obj X)) : Mono (E.ι.map (E.subι S)) := by
  rw [map_subι]
  infer_instance

instance mono_subι (S : Subfunctor (E.ι.obj X)) : Mono (E.subι S) :=
  have := E.fullyFaithful.faithful
  E.ι.mono_of_mono_map inferInstance

theorem range_map_subι (S : Subfunctor (E.ι.obj X)) :
    Subfunctor.range (E.ι.map (E.subι S)) = S := by
  refine le_antisymm ?_ fun b y hy => ⟨(E.subIso S).inv.app b ⟨y, hy⟩, ?_⟩
  · rw [map_subι]
    exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι S).le
  · rw [map_subι]
    exact congrArg Subtype.val
      (ConcreteCategory.congr_hom (congr_app (E.subIso S).inv_hom_id b) ⟨y, hy⟩)

def homOfLe {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) : E.sub S ⟶ E.sub T :=
  E.fullyFaithful.preimage ((E.subIso S).hom ≫ Subfunctor.homOfLe h ≫ (E.subIso T).inv)

@[reassoc (attr := simp)]
theorem homOfLe_subι {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) :
    E.homOfLe h ≫ E.subι T = E.subι S :=
  E.fullyFaithful.map_injective (by simp [homOfLe])

@[reassoc]
theorem map_homOfLe_subIso_hom {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) :
    E.ι.map (E.homOfLe h) ≫ (E.subIso T).hom = (E.subIso S).hom ≫ Subfunctor.homOfLe h := by
  simp [homOfLe]

instance mono_homOfLe {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) : Mono (E.homOfLe h) :=
  mono_of_mono_fac (E.homOfLe_subι h)

instance mono_map_homOfLe {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) :
    Mono (E.ι.map (E.homOfLe h)) :=
  mono_of_mono_fac (by rw [← Functor.map_comp, homOfLe_subι] : E.ι.map (E.homOfLe h) ≫
    E.ι.map (E.subι T) = E.ι.map (E.subι S))

theorem id_subι {Y : Bᵒᵖ ⥤ Type v} (S : Subfunctor Y) : (id B).subι S = S.ι := by
  dsimp only [subι, id]
  exact Category.id_comp _

theorem id_homOfLe {Y : Bᵒᵖ ⥤ Type v} {S T : Subfunctor Y} (h : S ≤ T) :
    (id B).homOfLe h = Subfunctor.homOfLe h := by
  dsimp only [homOfLe, id]
  exact (Category.id_comp _).trans (Category.comp_id _)

def IsBounded (α : Cardinal.{v}) (X : C) : Prop :=
  Atoms.Homotopical.IsBounded α (E.ι.obj X)

theorem isBounded_sub_iff (α : Cardinal.{v}) (S : Subfunctor (E.ι.obj X)) :
    E.IsBounded α (E.sub S) ↔ Atoms.Homotopical.IsBounded α S.toFunctor :=
  ⟨fun h => h.of_mono (E.subIso S).inv, fun h => h.of_mono (E.subIso S).hom⟩

theorem exists_boundedRepresentatives (α : Cardinal.{v}) :
    ∃ (ι : Type v) (R : ι → C), (∀ i, E.IsBounded α (R i)) ∧
      ∀ X : C, E.IsBounded α X → ∃ i, Nonempty (X ≅ R i) := by
  obtain ⟨ι, P, hP, hrep⟩ := Atoms.Homotopical.exists_boundedRepresentatives (A := B) α
  classical
  let ι' := {i : ι // ∃ X : C, Nonempty (E.ι.obj X ≅ P i)}
  refine ⟨ι', fun i => i.2.choose, fun i => (hP i.1).of_mono i.2.choose_spec.some.hom,
    fun X hX => ?_⟩
  obtain ⟨i, ⟨e⟩⟩ := hrep _ hX
  let j : ι' := ⟨i, X, ⟨e⟩⟩
  exact ⟨j, ⟨E.fullyFaithful.preimageIso (e ≪≫ j.2.choose_spec.some.symm)⟩⟩

variable (X) in
@[simps]
def subFunctor : Subfunctor (E.ι.obj X) ⥤ C where
  obj S := E.sub S
  map h := E.homOfLe (leOfHom h)
  map_id S := (cancel_mono (E.subι S)).1 (by simp)
  map_comp f g := (cancel_mono (E.subι _)).1 (by simp)

variable (X) in
def subFunctorCompIso : E.subFunctor X ⋙ E.ι ≅ Subfunctor.toFunctorFunctor (E.ι.obj X) :=
  NatIso.ofComponents (fun S => E.subIso S) fun h => E.map_homOfLe_subIso_hom (leOfHom h)

instance preservesColimitsOfShape_subFunctor {J : Type*} [Category J] [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (E.subFunctor X) := by
  have := E.fullyFaithful.full
  have := E.fullyFaithful.faithful
  have : PreservesColimitsOfShape J (E.subFunctor X ⋙ E.ι) :=
    preservesColimitsOfShape_of_natIso (E.subFunctorCompIso X).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (E.subFunctor X) E.ι

noncomputable def isColimitSubFunctorCocone {J : Type*} [Category J] [IsFilteredOrEmpty J]
    (G : J ⥤ Subfunctor (E.ι.obj X)) {T : Subfunctor (E.ι.obj X)}
    (hT : IsLUB (Set.range G.obj) T) :
    IsColimit ((E.subFunctor X).mapCocone (Preorder.coconeOfUpperBound G hT.1)) :=
  isColimitOfPreserves (E.subFunctor X) (Preorder.colimitCoconeOfIsLUB G hT).isColimit

theorem isPushout_homOfLe {A₁ A₂ A₃ A₄ : Subfunctor (E.ι.obj X)}
    (sq : Lattice.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (E.homOfLe sq.le₁₂) (E.homOfLe sq.le₁₃) (E.homOfLe sq.le₂₄)
      (E.homOfLe sq.le₃₄) := by
  have := E.fullyFaithful.full
  have := E.fullyFaithful.faithful
  refine IsPushout.of_map E.ι ((cancel_mono (E.subι A₄)).1 (by simp)) ?_
  exact (Subfunctor.isPushout_of_bicartSq sq).of_iso' (E.subIso _) (E.subIso _) (E.subIso _)
    (E.subIso _) (E.map_homOfLe_subIso_hom _).symm (E.map_homOfLe_subIso_hom _).symm
    (E.map_homOfLe_subIso_hom _).symm (E.map_homOfLe_subIso_hom _).symm

theorem transfiniteCompositionsOfShape_homOfLe {J : Type*} [LinearOrder J] [OrderBot J]
    [OrderTop J] [SuccOrder J] [WellFoundedLT J] (W : MorphismProperty C)
    (G : J → Subfunctor (E.ι.obj X)) (hG : Monotone G)
    (hlim : ∀ m : J, Order.IsSuccLimit m → G m = ⨆ k : Set.Iio m, G k)
    (hstep : ∀ j : J, ¬IsMax j → W (E.homOfLe (hG (Order.le_succ j)))) :
    W.transfiniteCompositionsOfShape J (E.homOfLe (hG bot_le : G ⊥ ≤ G ⊤)) := by
  have hc : hG.functor.IsWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨Preorder.isColimitOfIsLUB _ _ (by
      change IsLUB (Set.range fun k : Set.Iio m ↦ G k) (G m)
      rw [hlim m hm]
      apply isLUB_iSup)⟩⟩
  exact MorphismProperty.TransfiniteCompositionOfShape.mem _
    { F := hG.functor ⋙ E.subFunctor X
      isoBot := Iso.refl _
      isWellOrderContinuous :=
        ⟨fun m hm ↦ ⟨isColimitOfPreserves (E.subFunctor X)
          (Functor.isColimitOfIsWellOrderContinuous hG.functor m hm)⟩⟩
      incl :=
        { app j := E.homOfLe (hG le_top)
          naturality _ _ _ := (cancel_mono (E.subι _)).1 <| (Category.assoc _ _ _).trans <|
            (congrArg (_ ≫ ·) (E.homOfLe_subι _)).trans <| (E.homOfLe_subι _).trans <|
              (E.homOfLe_subι _).symm.trans
                (congrArg (· ≫ E.subι _) (Category.comp_id _).symm) }
      isColimit := isColimitOfPreserves (E.subFunctor X)
        (Preorder.colimitCoconeOfIsLUB hG.functor (pt := G ⊤)
          ⟨by rintro _ ⟨k, rfl⟩; exact hG le_top, fun _ hu ↦ hu ⟨⊤, rfl⟩⟩).isColimit
      map_mem j hj := hstep j hj
      fac := Category.id_comp _ }

theorem exists_map_homOfLe_app_eq {D : Type*} [Category D] (F : C ⥤ D ⥤ Type v)
    {ι : Type v} [Preorder ι] [IsFiltered ι] [PreservesColimitsOfShape ι F]
    (G : ι ⥤ Subfunctor (E.ι.obj X)) {T : Subfunctor (E.ι.obj X)}
    (hT : IsLUB (Set.range G.obj) T) {b : D} (z : (F.obj (E.sub T)).obj b) :
    ∃ (i : ι) (y : (F.obj (E.sub (G.obj i))).obj b),
      (F.map (E.homOfLe (hT.1 ⟨i, rfl⟩))).app b y = z := by
  let hc := isColimitOfPreserves ((evaluation D (Type v)).obj b)
    (isColimitOfPreserves F (E.isColimitSubFunctorCocone G hT))
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective _ hc z
  exact ⟨i, y, hy⟩

theorem range_map_subι_comp_le_of_isLUB {D : Type*} [Category D] (F : C ⥤ D ⥤ Type v)
    {ι : Type v} [Preorder ι] [IsFiltered ι] [PreservesColimitsOfShape ι F]
    (G : ι ⥤ Subfunctor (E.ι.obj X)) {T : Subfunctor (E.ι.obj X)}
    (hT : IsLUB (Set.range G.obj) T) {Y : D ⥤ Type v} (h : F.obj X ⟶ Y) (R : Subfunctor Y)
    (hR : ∀ i, Subfunctor.range (F.map (E.subι (G.obj i)) ≫ h) ≤ R) :
    Subfunctor.range (F.map (E.subι T) ≫ h) ≤ R := by
  rintro b _ ⟨z, rfl⟩
  obtain ⟨i, y, rfl⟩ := E.exists_map_homOfLe_app_eq F G hT z
  refine hR i b ⟨y, ?_⟩
  rw [← NatTrans.comp_app_apply, ← Category.assoc, ← F.map_comp, homOfLe_subι]

instance isIso_subι_top : IsIso (E.subι (⊤ : Subfunctor (E.ι.obj X))) := by
  have := E.fullyFaithful.full
  have := E.fullyFaithful.faithful
  have : IsIso (⊤ : Subfunctor (E.ι.obj X)).ι := (Subfunctor.eq_top_iff_isIso _).1 rfl
  have : IsIso (E.ι.map (E.subι (⊤ : Subfunctor (E.ι.obj X)))) := by
    rw [map_subι]
    infer_instance
  exact isIso_of_fully_faithful E.ι _

theorem isLUB_boundedSubfunctor {α : Cardinal.{v}} (hB : ∀ a b : B, Cardinal.mk (a ⟶ b) ≤ α)
    (X : C) :
    IsLUB (Set.range ((Subtype.mono_coe (fun S : Subfunctor (E.ι.obj X) =>
      Atoms.Homotopical.IsBounded α S.toFunctor)).functor.obj)) ⊤ := by
  rw [← iSup_boundedSubfunctor_eq_top hB (E.ι.obj X)]
  exact isLUB_iSup

noncomputable def isoSubRange {Z : C} (m : Z ⟶ X) [Mono (E.ι.map m)] :
    Z ≅ E.sub (Subfunctor.range (E.ι.map m)) :=
  E.fullyFaithful.preimageIso (asIso (Subfunctor.toRange (E.ι.map m)) ≪≫ (E.subIso _).symm)

@[reassoc (attr := simp)]
theorem isoSubRange_hom_subι {Z : C} (m : Z ⟶ X) [Mono (E.ι.map m)] :
    (E.isoSubRange m).hom ≫ E.subι _ = m :=
  E.fullyFaithful.map_injective (by simp [isoSubRange, Subfunctor.toRange_ι])

theorem exists_comp_eq_of_range_le {W Y Z : C} (m : W ⟶ Y) [Mono (E.ι.map m)] (f : Z ⟶ Y)
    (h : Subfunctor.range (E.ι.map f) ≤ Subfunctor.range (E.ι.map m)) :
    ∃ g : Z ⟶ W, g ≫ m = f := by
  obtain ⟨g, hg⟩ := Subfunctor.exists_comp_eq_of_range_le (E.ι.map m) (E.ι.map f) h
  exact ⟨E.fullyFaithful.preimage g, E.fullyFaithful.map_injective (by simp [hg])⟩

theorem range_map_subι_le_of_le {D : Type*} [Category D] (F : C ⥤ D ⥤ Type v)
    {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) :
    Subfunctor.range (F.map (E.subι S)) ≤ Subfunctor.range (F.map (E.subι T)) := by
  rw [← E.homOfLe_subι h, F.map_comp]
  exact Subfunctor.range_comp_le _ _

theorem homOfLe_mem_iff_of_eq (W : MorphismProperty C) {S₁ S₂ T₁ T₂ : Subfunctor (E.ι.obj X)}
    (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂) (hS : S₁ = S₂) (hT : T₁ = T₂) :
    W (E.homOfLe h₁) ↔ W (E.homOfLe h₂) := by
  subst hS hT
  rfl

theorem homOfLe_mem_of_eq (W : MorphismProperty C) [W.ContainsIdentities]
    {S T : Subfunctor (E.ι.obj X)} (h : S ≤ T) (hST : S = T) : W (E.homOfLe h) := by
  subst hST
  have : E.homOfLe h = 𝟙 _ := (cancel_mono (E.subι S)).1 (by simp)
  rw [this]
  exact W.id_mem _

variable {ι : Type v} [LinearOrder ι] {R : Subfunctor (E.ι.obj X)}
  {T : ι → Subfunctor (E.ι.obj X)} {F : WithTop ι → Subfunctor (E.ι.obj X)}

theorem subι_mem_of_isUnionChain [WellFoundedLT ι] [OrderBot (WithTop ι)]
    [SuccOrder (WithTop ι)] (hF : IsUnionChain R T F) (htop : F ⊤ = ⊤) (W : MorphismProperty C)
    [IsSaturated.{v} W]
    (hstep : ∀ z : ι, W (E.homOfLe (hF.mono (Order.le_succ (z : WithTop ι))))) :
    W (E.subι R) := by
  have hcomp := MorphismProperty.transfiniteCompositionsOfShape_le W _ _
    (E.transfiniteCompositionsOfShape_homOfLe W F hF.mono
      (fun _ hm ↦ hF.eq_iSup_of_isSuccLimit hm) fun j hj ↦ by
        induction j using WithTop.recTopCoe with
        | top => exact absurd isMax_top hj
        | coe z => exact hstep z)
  have hf : W (E.homOfLe (le_top : R ≤ ⊤)) :=
    (E.homOfLe_mem_iff_of_eq W (hF.mono bot_le) le_top hF.bot htop).1 hcomp
  rw [← E.homOfLe_subι (le_top : R ≤ ⊤)]
  exact MorphismProperty.comp_mem _ _ _ hf
    (isomorphisms_le_of_containsIdentities _ _ E.isIso_subι_top)

end BoundedEmbedding

end Atoms.Homotopical
