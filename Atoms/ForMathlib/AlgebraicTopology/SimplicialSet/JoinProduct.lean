import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

open CategoryTheory MonoidalCategory Opposite Simplicial CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory.DayConvolution

universe u

namespace SSet

open AugmentedSimplexCategory

private def augHom {m m' : SimplexCategory} (θ : m ⟶ m') :
    (WithInitial.of m : AugmentedSimplexCategory) ⟶ .of m' :=
  θ

private lemma join_map_joinMk {X Y : SSet.{u}} {n n' : SimplexCategoryᵒᵖ} (θ : n ⟶ n')
    {a b a' b' : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (h' : a' ⊗ b' = .of n'.unop)
    (f : a' ⟶ a) (g : b' ⟶ b)
    (hθ : augHom θ.unop ≫ eqToHom h.symm = eqToHom h'.symm ≫ (f ⊗ₘ g))
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b)) :
    (join X Y).map θ (joinMk h x y) =
      joinMk h' ((trivialAugmentation.obj X).map f.op x)
        ((trivialAugmentation.obj Y).map g.op y) := by
  let D := trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y
  have hu : D.map (f.op ⊗ₘ g.op) ((DayConvolution.unit (trivialAugmentation.obj X)
      (trivialAugmentation.obj Y)).app (op a, op b)
        ((x, y) : (trivialAugmentation.obj X).obj (op a) ×
          (trivialAugmentation.obj Y).obj (op b))) =
      (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y)).app
        (op a', op b') (((trivialAugmentation.obj X).map f.op x,
          (trivialAugmentation.obj Y).map g.op y) : (trivialAugmentation.obj X).obj (op a') ×
            (trivialAugmentation.obj Y).obj (op b')) :=
    (NatTrans.naturality_apply (DayConvolution.unit (trivialAugmentation.obj X)
      (trivialAugmentation.obj Y)) (X := (op a, op b)) (Y := (op a', op b')) (f.op, g.op) _).symm
  have e : (eqToHom h.symm).op ≫ (augHom θ.unop).op =
      (f.op ⊗ₘ g.op) ≫ (eqToHom h'.symm).op :=
    Quiver.Hom.unop_inj hθ
  change D.map (augHom θ.unop).op (D.map (eqToHom h.symm).op _) =
    D.map (eqToHom h'.symm).op _
  rw [← Functor.map_comp_apply, e, Functor.map_comp_apply, hu]

private def tensorAug {A K : SSet.{u}} : ∀ a : AugmentedSimplexCategory,
    (trivialAugmentation.obj A).obj (op a) → (trivialAugmentation.obj K).obj (op a) →
      (trivialAugmentation.obj (A ⊗ K)).obj (op a)
  | .star, _, _ => default
  | .of p, α, k => ((α, k) : (A ⊗ K).obj (op p))

private lemma tensorAug_map {A K : SSet.{u}} {a a' : AugmentedSimplexCategory} (f : a' ⟶ a)
    (α : (trivialAugmentation.obj A).obj (op a)) (k : (trivialAugmentation.obj K).obj (op a)) :
    tensorAug a' ((trivialAugmentation.obj A).map f.op α) ((trivialAugmentation.obj K).map f.op k) =
      (trivialAugmentation.obj (A ⊗ K)).map f.op (tensorAug a α k) := by
  cases a' with
  | star => exact Subsingleton.elim _ _
  | of p' =>
    cases a with
    | star => exact (WithInitial.false_of_to_star f).elim
    | of p => rfl

private lemma tensorAug_whiskerLeft {A K K' : SSet.{u}} (g : K ⟶ K') (a : AugmentedSimplexCategory)
    (α : (trivialAugmentation.obj A).obj (op a)) (k : (trivialAugmentation.obj K).obj (op a)) :
    tensorAug a α ((trivialAugmentation.map g).app _ k) =
      (trivialAugmentation.map (A ◁ g)).app _ (tensorAug a α k) := by
  cases a with
  | star => exact Subsingleton.elim _ _
  | of p => rfl

private def restrictAug (A : SSet.{u}) {n : SimplexCategoryᵒᵖ} {a b : AugmentedSimplexCategory}
    (h : a ⊗ b = .of n.unop) (α : A.obj n) : (trivialAugmentation.obj A).obj (op a) :=
  (trivialAugmentation.obj A).map (inl a b ≫ eqToHom h).op
    (α : (trivialAugmentation.obj A).obj (op (.of n.unop)))

private lemma restrictAug_map (A : SSet.{u}) {n n' : SimplexCategoryᵒᵖ} (θ : n ⟶ n')
    {a b a' b' : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (h' : a' ⊗ b' = .of n'.unop)
    (f : a' ⟶ a) (g : b' ⟶ b)
    (hθ : augHom θ.unop ≫ eqToHom h.symm = eqToHom h'.symm ≫ (f ⊗ₘ g)) (α : A.obj n) :
    (trivialAugmentation.obj A).map f.op (restrictAug A h α) = restrictAug A h' (A.map θ α) := by
  have e : augHom θ.unop = (eqToHom h'.symm ≫ (f ⊗ₘ g)) ≫ eqToHom h := by
    rw [← hθ, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have e' : f ≫ inl a b ≫ eqToHom h = inl a' b' ≫ eqToHom h' ≫ augHom θ.unop := by
    rw [e]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (inl a' b') (f ⊗ₘ g), inl_comp_tensorHom, Category.assoc]
  refine (Functor.map_comp_apply _ _ _ _).symm.trans (Eq.trans ?_
    (Functor.map_comp_apply (trivialAugmentation.obj A) (augHom θ.unop).op _
      (α : (trivialAugmentation.obj A).obj (op (.of n.unop)))))
  rw [← op_comp, ← op_comp, e', Category.assoc]

private lemma inl_star_comp_eqToHom (x : AugmentedSimplexCategory) (h : x ⊗ .star = x) :
    inl x .star ≫ eqToHom h = 𝟙 x :=
  toFun_injective (funext fun i ↦ Fin.ext (by
    rw [toFun_comp_apply, val_toFun_eqToHom, val_toFun_inl, toFun_id]))

private lemma restrictAug_star_right (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) (α : A.obj n)
    (h : (WithInitial.of n.unop : AugmentedSimplexCategory) ⊗ .star = .of n.unop) :
    restrictAug A h α = α := by
  dsimp only [restrictAug]
  rw [inl_star_comp_eqToHom, op_id]
  exact Functor.map_id_apply _ _ _

private lemma bijective_joinMk (X Y : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (fun p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = .of n.unop}, (trivialAugmentation.obj X).obj (op s.1.1) ×
          (trivialAugmentation.obj Y).obj (op s.1.2) ↦ joinMk p.1.2 p.2.1 p.2.2) :=
  bijective_map_unit_app _ _ _

private noncomputable def tensorJoinSigma (A K L : SSet.{u}) (n : SimplexCategoryᵒᵖ) (α : A.obj n)
    (p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory // s.1 ⊗ s.2 = .of n.unop},
      (trivialAugmentation.obj K).obj (op s.1.1) × (trivialAugmentation.obj L).obj (op s.1.2)) :
    (join (A ⊗ K) L).obj n :=
  joinMk p.1.2 (tensorAug _ (restrictAug A p.1.2 α) p.2.1) p.2.2

private noncomputable def tensorJoinApp (A K L : SSet.{u}) (n : SimplexCategoryᵒᵖ) (α : A.obj n)
    (t : (join K L).obj n) : (join (A ⊗ K) L).obj n :=
  tensorJoinSigma A K L n α ((Equiv.ofBijective _ (bijective_joinMk K L n)).symm t)

private lemma tensorJoinApp_joinMk (A K L : SSet.{u}) {n : SimplexCategoryᵒᵖ} (α : A.obj n)
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (k : (trivialAugmentation.obj K).obj (op a)) (l : (trivialAugmentation.obj L).obj (op b)) :
    tensorJoinApp A K L n α (joinMk h k l) = joinMk h (tensorAug a (restrictAug A h α) k) l := by
  have : (Equiv.ofBijective _ (bijective_joinMk K L n)).symm (joinMk h k l) =
      ⟨⟨(a, b), h⟩, k, l⟩ :=
    (Equiv.ofBijective _ (bijective_joinMk K L n)).symm_apply_apply ⟨⟨(a, b), h⟩, k, l⟩
  exact congrArg (tensorJoinSigma A K L n α) this

noncomputable def tensorJoinMap (A K L : SSet.{u}) : A ⊗ join K L ⟶ join (A ⊗ K) L where
  app n := TypeCat.ofHom fun z ↦ tensorJoinApp A K L n z.1 z.2
  naturality n n' θ := by
    ext ⟨α, t⟩
    obtain ⟨a, b, h, k, l, rfl⟩ := exists_joinMk t
    obtain ⟨⟨⟨⟨a', b'⟩, h'⟩, f, g⟩, hfg⟩ := (bijective_eqToHom_comp_tensorHom (.of n'.unop) a b).2
      (augHom θ.unop ≫ eqToHom h.symm)
    change tensorJoinApp A K L n' (A.map θ α) ((join K L).map θ (joinMk h k l)) =
      (join (A ⊗ K) L).map θ (tensorJoinApp A K L n α (joinMk h k l))
    rw [tensorJoinApp_joinMk, join_map_joinMk θ h h' f g hfg.symm,
      join_map_joinMk θ h h' f g hfg.symm, tensorJoinApp_joinMk, ← tensorAug_map,
      restrictAug_map A θ h h' f g hfg.symm]

@[reassoc]
theorem whiskerLeft_joinInclLeft_comp_tensorJoinMap (A K L : SSet.{u}) :
    A ◁ joinInclLeft K L ≫ tensorJoinMap A K L = joinInclLeft (A ⊗ K) L := by
  ext n ⟨α, k⟩
  have e (X Y : SSet.{u}) (x : X.obj n)
      (h : (WithInitial.of n.unop : AugmentedSimplexCategory) ⊗ .star = .of n.unop) :
      (joinInclLeft X Y).app n x = joinMk h x default :=
    (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
      (op (.of n.unop)) _).symm
  change tensorJoinApp A K L n α ((joinInclLeft K L).app n k) =
    (joinInclLeft (A ⊗ K) L).app n (α, k)
  have h : (WithInitial.of n.unop : AugmentedSimplexCategory) ⊗ .star = .of n.unop := rfl
  rw [e K L k h, e (A ⊗ K) L (α, k) h]
  refine (tensorJoinApp_joinMk A K L α h k default).trans ?_
  rw [restrictAug_star_right]
  rfl

@[reassoc]
theorem whiskerLeft_joinInclRight_comp_tensorJoinMap (A K L : SSet.{u}) :
    A ◁ joinInclRight K L ≫ tensorJoinMap A K L = snd A L ≫ joinInclRight (A ⊗ K) L := by
  ext n ⟨α, l⟩
  have e (X Y : SSet.{u}) (y : Y.obj n)
      (h : (WithInitial.star : AugmentedSimplexCategory) ⊗ .of n.unop = .of n.unop) :
      (joinInclRight X Y).app n y = joinMk h default y :=
    (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
      (op (.of n.unop)) _).symm
  change tensorJoinApp A K L n α ((joinInclRight K L).app n l) = (joinInclRight (A ⊗ K) L).app n l
  have h : (WithInitial.star : AugmentedSimplexCategory) ⊗ .of n.unop = .of n.unop := rfl
  rw [e K L l h, e (A ⊗ K) L l h]
  exact tensorJoinApp_joinMk A K L α h default l

@[reassoc]
theorem whiskerLeft_joinMap_comp_tensorJoinMap (A : SSet.{u}) {K K' L L' : SSet.{u}} (f : K ⟶ K')
    (g : L ⟶ L') :
    A ◁ joinMap f g ≫ tensorJoinMap A K' L' = tensorJoinMap A K L ≫ joinMap (A ◁ f) g := by
  ext n ⟨α, t⟩
  obtain ⟨a, b, h, k, l, rfl⟩ := exists_joinMk t
  change tensorJoinApp A K' L' n α ((joinMap f g).app n (joinMk h k l)) =
    (joinMap (A ◁ f) g).app n (tensorJoinApp A K L n α (joinMk h k l))
  rw [joinMap_app_joinMk, tensorJoinApp_joinMk, tensorJoinApp_joinMk, joinMap_app_joinMk,
    tensorAug_whiskerLeft]

private def restrictAugRight (A : SSet.{u}) {n : SimplexCategoryᵒᵖ}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (α : A.obj n) :
    (trivialAugmentation.obj A).obj (op b) :=
  (trivialAugmentation.obj A).map (inr a b ≫ eqToHom h).op
    (α : (trivialAugmentation.obj A).obj (op (.of n.unop)))

private lemma restrictAugRight_map (A : SSet.{u}) {n n' : SimplexCategoryᵒᵖ} (θ : n ⟶ n')
    {a b a' b' : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (h' : a' ⊗ b' = .of n'.unop)
    (f : a' ⟶ a) (g : b' ⟶ b)
    (hθ : augHom θ.unop ≫ eqToHom h.symm = eqToHom h'.symm ≫ (f ⊗ₘ g)) (α : A.obj n) :
    (trivialAugmentation.obj A).map g.op (restrictAugRight A h α) =
      restrictAugRight A h' (A.map θ α) := by
  have e : augHom θ.unop = (eqToHom h'.symm ≫ (f ⊗ₘ g)) ≫ eqToHom h := by
    rw [← hθ, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have e' : g ≫ inr a b ≫ eqToHom h = inr a' b' ≫ eqToHom h' ≫ augHom θ.unop := by
    rw [e]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (inr a' b') (f ⊗ₘ g), inr_comp_tensorHom, Category.assoc]
  refine (Functor.map_comp_apply _ _ _ _).symm.trans (Eq.trans ?_
    (Functor.map_comp_apply (trivialAugmentation.obj A) (augHom θ.unop).op _
      (α : (trivialAugmentation.obj A).obj (op (.of n.unop)))))
  rw [← op_comp, ← op_comp, e', Category.assoc]

private lemma inr_star_comp_eqToHom (x : AugmentedSimplexCategory) (h : .star ⊗ x = x) :
    inr .star x ≫ eqToHom h = 𝟙 x :=
  toFun_injective (funext fun i ↦ Fin.ext (by
    rw [toFun_comp_apply, val_toFun_eqToHom, val_toFun_inr, toFun_id]
    exact Nat.zero_add _))

private lemma restrictAugRight_star_left (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) (α : A.obj n)
    (h : (WithInitial.star : AugmentedSimplexCategory) ⊗ .of n.unop = .of n.unop) :
    restrictAugRight A h α = α := by
  dsimp only [restrictAugRight]
  rw [inr_star_comp_eqToHom, op_id]
  exact Functor.map_id_apply _ _ _

private lemma restrictAug_app {A A' : SSet.{u}} (φ : A ⟶ A') {n : SimplexCategoryᵒᵖ}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (α : A.obj n) :
    (trivialAugmentation.map φ).app _ (restrictAug A h α) = restrictAug A' h (φ.app n α) :=
  NatTrans.naturality_apply (trivialAugmentation.map φ) _ _

private lemma restrictAugRight_app {A A' : SSet.{u}} (φ : A ⟶ A') {n : SimplexCategoryᵒᵖ}
    {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop) (α : A.obj n) :
    (trivialAugmentation.map φ).app _ (restrictAugRight A h α) =
      restrictAugRight A' h (φ.app n α) :=
  NatTrans.naturality_apply (trivialAugmentation.map φ) _ _

private lemma tensorAug_whiskerRight {A A' K : SSet.{u}} (φ : A ⟶ A')
    (a : AugmentedSimplexCategory) (α : (trivialAugmentation.obj A).obj (op a))
    (k : (trivialAugmentation.obj K).obj (op a)) :
    tensorAug a ((trivialAugmentation.map φ).app _ α) k =
      (trivialAugmentation.map (φ ▷ K)).app _ (tensorAug a α k) := by
  cases a with
  | star => exact Subsingleton.elim _ _
  | of p => rfl

private noncomputable def tensorJoinTensorSigma (A K L : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (α : A.obj n)
    (p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory // s.1 ⊗ s.2 = .of n.unop},
      (trivialAugmentation.obj K).obj (op s.1.1) × (trivialAugmentation.obj L).obj (op s.1.2)) :
    (join (A ⊗ K) (A ⊗ L)).obj n :=
  joinMk p.1.2 (tensorAug _ (restrictAug A p.1.2 α) p.2.1)
    (tensorAug _ (restrictAugRight A p.1.2 α) p.2.2)

private noncomputable def tensorJoinTensorApp (A K L : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (α : A.obj n) (t : (join K L).obj n) : (join (A ⊗ K) (A ⊗ L)).obj n :=
  tensorJoinTensorSigma A K L n α ((Equiv.ofBijective _ (bijective_joinMk K L n)).symm t)

private lemma tensorJoinTensorApp_joinMk (A K L : SSet.{u}) {n : SimplexCategoryᵒᵖ}
    (α : A.obj n) {a b : AugmentedSimplexCategory} (h : a ⊗ b = .of n.unop)
    (k : (trivialAugmentation.obj K).obj (op a)) (l : (trivialAugmentation.obj L).obj (op b)) :
    tensorJoinTensorApp A K L n α (joinMk h k l) =
      joinMk h (tensorAug a (restrictAug A h α) k) (tensorAug b (restrictAugRight A h α) l) := by
  have : (Equiv.ofBijective _ (bijective_joinMk K L n)).symm (joinMk h k l) =
      ⟨⟨(a, b), h⟩, k, l⟩ :=
    (Equiv.ofBijective _ (bijective_joinMk K L n)).symm_apply_apply ⟨⟨(a, b), h⟩, k, l⟩
  exact congrArg (tensorJoinTensorSigma A K L n α) this

noncomputable def tensorJoinTensorMap (A K L : SSet.{u}) :
    A ⊗ join K L ⟶ join (A ⊗ K) (A ⊗ L) where
  app n := TypeCat.ofHom fun z ↦ tensorJoinTensorApp A K L n z.1 z.2
  naturality n n' θ := by
    ext ⟨α, t⟩
    obtain ⟨a, b, h, k, l, rfl⟩ := exists_joinMk t
    obtain ⟨⟨⟨⟨a', b'⟩, h'⟩, f, g⟩, hfg⟩ := (bijective_eqToHom_comp_tensorHom (.of n'.unop) a b).2
      (augHom θ.unop ≫ eqToHom h.symm)
    change tensorJoinTensorApp A K L n' (A.map θ α) ((join K L).map θ (joinMk h k l)) =
      (join (A ⊗ K) (A ⊗ L)).map θ (tensorJoinTensorApp A K L n α (joinMk h k l))
    rw [tensorJoinTensorApp_joinMk, join_map_joinMk θ h h' f g hfg.symm,
      join_map_joinMk θ h h' f g hfg.symm, tensorJoinTensorApp_joinMk, ← tensorAug_map,
      ← tensorAug_map, restrictAug_map A θ h h' f g hfg.symm,
      restrictAugRight_map A θ h h' f g hfg.symm]

@[reassoc]
theorem whiskerLeft_joinInclLeft_comp_tensorJoinTensorMap (A K L : SSet.{u}) :
    A ◁ joinInclLeft K L ≫ tensorJoinTensorMap A K L = joinInclLeft (A ⊗ K) (A ⊗ L) := by
  ext n ⟨α, k⟩
  have e (X Y : SSet.{u}) (x : X.obj n)
      (h : (WithInitial.of n.unop : AugmentedSimplexCategory) ⊗ .star = .of n.unop) :
      (joinInclLeft X Y).app n x = joinMk h x default :=
    (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
      (op (.of n.unop)) _).symm
  change tensorJoinTensorApp A K L n α ((joinInclLeft K L).app n k) =
    (joinInclLeft (A ⊗ K) (A ⊗ L)).app n (α, k)
  have h : (WithInitial.of n.unop : AugmentedSimplexCategory) ⊗ .star = .of n.unop := rfl
  rw [e K L k h, e (A ⊗ K) (A ⊗ L) (α, k) h]
  refine (tensorJoinTensorApp_joinMk A K L α h k default).trans ?_
  rw [restrictAug_star_right]
  exact congrArg (joinMk h _) (Subsingleton.elim _ _)

@[reassoc]
theorem whiskerLeft_joinInclRight_comp_tensorJoinTensorMap (A K L : SSet.{u}) :
    A ◁ joinInclRight K L ≫ tensorJoinTensorMap A K L = joinInclRight (A ⊗ K) (A ⊗ L) := by
  ext n ⟨α, l⟩
  have e (X Y : SSet.{u}) (y : Y.obj n)
      (h : (WithInitial.star : AugmentedSimplexCategory) ⊗ .of n.unop = .of n.unop) :
      (joinInclRight X Y).app n y = joinMk h default y :=
    (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
      (op (.of n.unop)) _).symm
  change tensorJoinTensorApp A K L n α ((joinInclRight K L).app n l) =
    (joinInclRight (A ⊗ K) (A ⊗ L)).app n (α, l)
  have h : (WithInitial.star : AugmentedSimplexCategory) ⊗ .of n.unop = .of n.unop := rfl
  rw [e K L l h, e (A ⊗ K) (A ⊗ L) (α, l) h]
  refine (tensorJoinTensorApp_joinMk A K L α h default l).trans ?_
  rw [restrictAugRight_star_left]
  exact congrArg (joinMk h · _) (Subsingleton.elim _ _)

@[reassoc]
theorem whiskerRight_comp_tensorJoinTensorMap {A A' : SSet.{u}} (φ : A ⟶ A') (K L : SSet.{u}) :
    φ ▷ join K L ≫ tensorJoinTensorMap A' K L =
      tensorJoinTensorMap A K L ≫ joinMap (φ ▷ K) (φ ▷ L) := by
  ext n ⟨α, t⟩
  obtain ⟨a, b, h, k, l, rfl⟩ := exists_joinMk t
  change tensorJoinTensorApp A' K L n (φ.app n α) (joinMk h k l) =
    (joinMap (φ ▷ K) (φ ▷ L)).app n (tensorJoinTensorApp A K L n α (joinMk h k l))
  rw [tensorJoinTensorApp_joinMk, tensorJoinTensorApp_joinMk, joinMap_app_joinMk,
    ← tensorAug_whiskerRight, ← tensorAug_whiskerRight, restrictAug_app, restrictAugRight_app]

end SSet
