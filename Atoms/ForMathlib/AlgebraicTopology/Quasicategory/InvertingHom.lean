import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite
  MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe u

namespace SSet

section Swap

noncomputable def ihomSwap (A B X : SSet.{u}) :
    (A ⟶ (ihom B).obj X) ≃ (B ⟶ (ihom A).obj X) where
  toFun f := curry ((β_ A B).hom ≫ uncurry f)
  invFun g := curry ((β_ B A).hom ≫ uncurry g)
  left_inv f := by
    dsimp only
    rw [uncurry_curry, SymmetricCategory.symmetry_assoc, curry_uncurry]
  right_inv g := by
    dsimp only
    rw [uncurry_curry, SymmetricCategory.symmetry_assoc, curry_uncurry]

lemma ihomSwap_apply {A B X : SSet.{u}} (f : A ⟶ (ihom B).obj X) :
    ihomSwap A B X f = curry ((β_ A B).hom ≫ uncurry f) := rfl

lemma ihomSwap_comp_ihom_map {A B X Y : SSet.{u}} (f : A ⟶ (ihom B).obj X) (p : X ⟶ Y) :
    ihomSwap A B Y (f ≫ (ihom B).map p) = ihomSwap A B X f ≫ (ihom A).map p := by
  rw [ihomSwap_apply, ihomSwap_apply, uncurry_natural_right, ← curry_natural_right,
    Category.assoc]

lemma ihomSwap_comp_pre_app {A B B' X : SSet.{u}} (f : A ⟶ (ihom B).obj X) (i : B' ⟶ B) :
    ihomSwap A B' X (f ≫ (pre i).app X) = i ≫ ihomSwap A B X f := by
  rw [ihomSwap_apply, ihomSwap_apply, uncurry_pre_app, ← curry_natural_left,
    BraidedCategory.braiding_naturality_right_assoc]

lemma ihomSwap_comp {A A' B X : SSet.{u}} (j : A' ⟶ A) (f : A ⟶ (ihom B).obj X) :
    ihomSwap A' B X (j ≫ f) = ihomSwap A B X f ≫ (pre j).app X := by
  rw [ihomSwap_apply, ihomSwap_apply, uncurry_natural_left, curry_pre_app,
    BraidedCategory.braiding_naturality_left_assoc]

lemma ihomSwap_comp_evalVertex {A B X : SSet.{u}} (f : A ⟶ (ihom B).obj X) (a : A _⦋0⦌) :
    ihomSwap A B X f ≫ evalVertex a X = ihomPointEquiv B X (yonedaEquiv.symm a ≫ f) := by
  rw [comp_evalVertex, ihomSwap_apply, uncurry_curry, lift_braiding_hom_assoc,
    ihomPointEquiv_apply, uncurry_natural_left, lift_whiskerLeft_assoc]

end Swap

section InvertingHom

def invertingHom (B X : SSet.{u}) : ((ihom B).obj X).Subcomplex where
  obj n := {σ | ∀ j : Fin (n.unop.len + 1),
    Subcomplex.range (ihomPointEquiv B X (yonedaEquiv.symm
      (((ihom B).obj X).map (SimplexCategory.const ⦋0⦌ n.unop j).op σ))) ≤ X.core}
  map {n m} θ σ hσ j := by
    have h := hσ (θ.unop.toOrderHom j)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

lemma range_le_invertingHom_iff_forall {B X Z : SSet.{u}} (g : Z ⟶ (ihom B).obj X) :
    Subcomplex.range g ≤ invertingHom B X ↔
      ∀ z : Z _⦋0⦌, Subcomplex.range (ihomPointEquiv B X (yonedaEquiv.symm z ≫ g)) ≤ X.core := by
  have hy {m : ℕ} (z : Z _⦋m⦌) : yonedaEquiv.symm (g.app _ z) = yonedaEquiv.symm z ≫ g :=
    yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  constructor
  · intro h z
    have hz := h _ ⟨z, rfl⟩ 0
    rwa [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 _), op_id,
      Functor.map_id_apply, hy] at hz
  · rintro h n _ ⟨σ, rfl⟩ j
    rw [← NatTrans.naturality_apply, hy]
    exact h _

theorem range_le_invertingHom_iff {A B X : SSet.{u}} (f : A ⟶ (ihom B).obj X) :
    Subcomplex.range f ≤ invertingHom B X ↔
      Subcomplex.range (ihomSwap A B X f) ≤ objectwiseCore A X := by
  rw [range_le_invertingHom_iff_forall, range_le_objectwiseCore_iff_forall]
  simp only [ihomSwap_comp_evalVertex]

private lemma range_comp_ι_le {Z W : SSet.{u}} {S : W.Subcomplex} (g : Z ⟶ (S : SSet.{u})) :
    Subcomplex.range (g ≫ S.ι) ≤ S := by
  rintro n _ ⟨σ, rfl⟩
  exact (g.app n σ).2

noncomputable def invertingHomEquiv (A B X : SSet.{u}) :
    (A ⟶ (invertingHom B X : SSet.{u})) ≃ (B ⟶ (objectwiseCore A X : SSet.{u})) where
  toFun g := Subcomplex.lift (ihomSwap A B X (g ≫ (invertingHom B X).ι))
    ((range_le_invertingHom_iff _).1 (range_comp_ι_le g))
  invFun l := Subcomplex.lift ((ihomSwap A B X).symm (l ≫ (objectwiseCore A X).ι))
    ((range_le_invertingHom_iff _).2 (by
      rw [Equiv.apply_symm_apply]
      exact range_comp_ι_le l))
  left_inv g := by
    rw [← cancel_mono (invertingHom B X).ι, Subcomplex.lift_ι, Subcomplex.lift_ι,
      Equiv.symm_apply_apply]
  right_inv l := by
    rw [← cancel_mono (objectwiseCore A X).ι, Subcomplex.lift_ι, Subcomplex.lift_ι,
      Equiv.apply_symm_apply]

@[reassoc (attr := simp)]
lemma invertingHomEquiv_apply_ι {A B X : SSet.{u}} (g : A ⟶ (invertingHom B X : SSet.{u})) :
    invertingHomEquiv A B X g ≫ (objectwiseCore A X).ι =
      ihomSwap A B X (g ≫ (invertingHom B X).ι) :=
  rfl

@[reassoc (attr := simp)]
lemma invertingHomEquiv_symm_apply_ι {A B X : SSet.{u}}
    (l : B ⟶ (objectwiseCore A X : SSet.{u})) :
    (invertingHomEquiv A B X).symm l ≫ (invertingHom B X).ι =
      (ihomSwap A B X).symm (l ≫ (objectwiseCore A X).ι) :=
  rfl

end InvertingHom

section Restriction

noncomputable def invertingHomMap (B : SSet.{u}) {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    (invertingHom B X : SSet.{u}) ⟶ (invertingHom B Y : SSet.{u}) :=
  Subcomplex.lift ((invertingHom B X).ι ≫ (ihom B).map p) (by
    refine (range_le_invertingHom_iff_forall _).2 fun z ↦ ?_
    have hz := (range_le_invertingHom_iff_forall _).1 (range_comp_ι_le (𝟙 _)) z
    rw [Category.id_comp] at hz
    rw [← Category.assoc, ihomPointEquiv_comp_ihom_map, ← Subcomplex.lift_ι _ hz,
      Category.assoc]
    exact (Subfunctor.range_comp_le _ _).trans (range_core_ι_comp_le_core p))

@[reassoc (attr := simp)]
lemma invertingHomMap_ι (B : SSet.{u}) {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    invertingHomMap B p ≫ (invertingHom B Y).ι = (invertingHom B X).ι ≫ (ihom B).map p :=
  Subcomplex.lift_ι _ _

noncomputable def invertingHomPre {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    (invertingHom B X : SSet.{u}) ⟶ (invertingHom A X : SSet.{u}) :=
  Subcomplex.lift ((invertingHom B X).ι ≫ (pre i).app X) (by
    refine (range_le_invertingHom_iff_forall _).2 fun z ↦ ?_
    have hz := (range_le_invertingHom_iff_forall _).1 (range_comp_ι_le (𝟙 _)) z
    rw [Category.id_comp] at hz
    rw [← Category.assoc, ihomPointEquiv_comp_pre_app]
    exact (Subfunctor.range_comp_le _ _).trans hz)

@[reassoc (attr := simp)]
lemma invertingHomPre_ι {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    invertingHomPre i X ≫ (invertingHom A X).ι = (invertingHom B X).ι ≫ (pre i).app X :=
  Subcomplex.lift_ι _ _

noncomputable def invertingHomRestrict {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y)
    {A B : SSet.{u}} (i : A ⟶ B) :
    (invertingHom B X : SSet.{u}) ⟶ pullback (invertingHomMap A p) (invertingHomPre i Y) :=
  pullback.lift (invertingHomPre i X) (invertingHomMap B p) (by
    rw [← cancel_mono (invertingHom A Y).ι, Category.assoc, Category.assoc, invertingHomMap_ι,
      invertingHomPre_ι_assoc, invertingHomPre_ι, invertingHomMap_ι_assoc, pre_comm_ihom_map])

@[reassoc (attr := simp)]
lemma invertingHomRestrict_fst {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) {A B : SSet.{u}}
    (i : A ⟶ B) : invertingHomRestrict p i ≫ pullback.fst _ _ = invertingHomPre i X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma invertingHomRestrict_snd {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) {A B : SSet.{u}}
    (i : A ⟶ B) : invertingHomRestrict p i ≫ pullback.snd _ _ = invertingHomMap B p :=
  pullback.lift_snd _ _ _

theorem hasLiftingProperty_invertingHomRestrict {X Y : SSet.{u}} [X.Quasicategory]
    (p : X ⟶ Y) {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    (h : HasLiftingProperty i (objectwiseCoreRestrict p j)) :
    HasLiftingProperty j (invertingHomRestrict p i) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  let b₁ : L ⟶ (invertingHom A X : SSet.{u}) := b ≫ pullback.fst _ _
  let b₂ : L ⟶ (invertingHom B Y : SSet.{u}) := b ≫ pullback.snd _ _
  have hfst : j ≫ b₁ ≫ (invertingHom A X).ι = a ≫ (invertingHom B X).ι ≫ (pre i).app X := by
    rw [← invertingHomPre_ι, ← invertingHomRestrict_fst_assoc, ← Category.assoc a, sq.w]
    simp only [b₁, Category.assoc]
  have hsnd : j ≫ b₂ ≫ (invertingHom B Y).ι = a ≫ (invertingHom B X).ι ≫ (ihom B).map p := by
    rw [← invertingHomMap_ι, ← invertingHomRestrict_snd_assoc, ← Category.assoc a, sq.w]
    simp only [b₂, Category.assoc]
  have hb : b₁ ≫ (invertingHom A X).ι ≫ (ihom A).map p =
      b₂ ≫ (invertingHom B Y).ι ≫ (pre i).app Y := by
    rw [← invertingHomMap_ι, ← invertingHomPre_ι]
    simp only [b₁, b₂, Category.assoc, pullback.condition_assoc]
  let top : A ⟶ (objectwiseCore L X : SSet.{u}) := invertingHomEquiv L A X b₁
  let bot₁ : B ⟶ (objectwiseCore K X : SSet.{u}) := invertingHomEquiv K B X a
  let bot₂ : B ⟶ (objectwiseCore L Y : SSet.{u}) := invertingHomEquiv L B Y b₂
  have hbot : bot₁ ≫ objectwiseCoreMap K p = bot₂ ≫ objectwiseCorePre j Y := by
    rw [← cancel_mono (objectwiseCore K Y).ι, Category.assoc, Category.assoc,
      objectwiseCoreMap_ι, objectwiseCorePre_ι, invertingHomEquiv_apply_ι_assoc,
      invertingHomEquiv_apply_ι_assoc, ← ihomSwap_comp_ihom_map, ← ihomSwap_comp,
      Category.assoc, hsnd]
  let bot : B ⟶ pullback (objectwiseCoreMap K p) (objectwiseCorePre j Y) :=
    pullback.lift bot₁ bot₂ hbot
  have sq' : CommSq top i (objectwiseCoreRestrict p j) bot := ⟨by
    refine pullback.hom_ext ?_ ?_
    · rw [← cancel_mono (objectwiseCore K X).ι]
      simp only [bot, top, bot₁, Category.assoc, objectwiseCoreRestrict_fst, pullback.lift_fst,
        objectwiseCorePre_ι, invertingHomEquiv_apply_ι, invertingHomEquiv_apply_ι_assoc]
      rw [← ihomSwap_comp, ← ihomSwap_comp_pre_app, hfst, Category.assoc]
    · rw [← cancel_mono (objectwiseCore L Y).ι]
      simp only [bot, top, bot₂, Category.assoc, objectwiseCoreRestrict_snd, pullback.lift_snd,
        objectwiseCoreMap_ι, invertingHomEquiv_apply_ι, invertingHomEquiv_apply_ι_assoc]
      rw [← ihomSwap_comp_ihom_map, ← ihomSwap_comp_pre_app, Category.assoc, hb]
      exact congrArg _ (Category.assoc _ _ _).symm⟩
  obtain ⟨l⟩ := (h.sq_hasLift sq').exists_lift
  let m : L ⟶ (invertingHom B X : SSet.{u}) := (invertingHomEquiv L B X).symm l.l
  have hm : ihomSwap L B X (m ≫ (invertingHom B X).ι) = l.l ≫ (objectwiseCore L X).ι := by
    rw [invertingHomEquiv_symm_apply_ι, Equiv.apply_symm_apply]
  refine ⟨⟨⟨m, ?_, ?_⟩⟩⟩
  · rw [← cancel_mono (invertingHom B X).ι, Category.assoc]
    refine (ihomSwap K B X).injective ?_
    rw [ihomSwap_comp, hm, Category.assoc, ← objectwiseCorePre_ι,
      ← objectwiseCoreRestrict_fst_assoc, ← Category.assoc l.l, l.fac_right]
    simp only [bot, bot₁, pullback.lift_fst_assoc, invertingHomEquiv_apply_ι]
  · refine pullback.hom_ext ?_ ?_
    · rw [← cancel_mono (invertingHom A X).ι, Category.assoc, Category.assoc,
        invertingHomRestrict_fst_assoc, invertingHomPre_ι]
      refine (ihomSwap L A X).injective ?_
      rw [← Category.assoc, ihomSwap_comp_pre_app, hm, ← Category.assoc, l.fac_left]
      simp only [top, b₁, invertingHomEquiv_apply_ι, Category.assoc]
    · rw [← cancel_mono (invertingHom B Y).ι, Category.assoc, Category.assoc,
        invertingHomRestrict_snd_assoc, invertingHomMap_ι]
      refine (ihomSwap L B Y).injective ?_
      rw [← Category.assoc, ihomSwap_comp_ihom_map, hm, Category.assoc, ← objectwiseCoreMap_ι,
        ← objectwiseCoreRestrict_snd_assoc, ← Category.assoc l.l, l.fac_right]
      simp only [bot, bot₂, b₂, pullback.lift_snd_assoc, invertingHomEquiv_apply_ι,
        Category.assoc]

theorem trivialFibration_invertingHom_restrict {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Isofibration p] {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) :
    modelCategoryQuillen.I.rlp (invertingHomRestrict p i) := by
  rintro _ _ _ ⟨n⟩
  refine hasLiftingProperty_invertingHomRestrict p i _ ?_
  rw [anodyneExtensions_eq_llp_rlp] at hi
  exact hi _ (kanFibration_objectwiseCore_restrict p (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι)

end Restriction

end SSet
