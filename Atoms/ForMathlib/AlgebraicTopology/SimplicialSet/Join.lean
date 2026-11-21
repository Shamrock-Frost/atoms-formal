import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Monoidal.Opposite

open CategoryTheory MonoidalCategory Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution
  CategoryTheory.MonoidalCategory.ExternalProduct

universe u

namespace AugmentedSimplexCategory

noncomputable instance dayConvolution (X Y : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :
    DayConvolution X Y :=
  .ofHasPointwiseLeftKanExtension X Y

private noncomputable def decomposition (n x y : AugmentedSimplexCategory) :
    (n ⟶ x ⊗ y) ≃ Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = n}, (s.1.1 ⟶ x) × (s.1.2 ⟶ y) :=
  (Equiv.ofBijective _ (bijective_eqToHom_comp_tensorHom n x y)).symm

private lemma decomposition_eqToHom_comp_tensorHom {n x y a b : AugmentedSimplexCategory}
    (h : a ⊗ b = n) (f : a ⟶ x) (g : b ⟶ y) :
    decomposition n x y (eqToHom h.symm ≫ (f ⊗ₘ g)) = ⟨⟨(a, b), h⟩, f, g⟩ :=
  (Equiv.symm_apply_eq _).2 rfl

private lemma map_app_map_unit_app {X X' Y Y' : AugmentedSimplexCategoryᵒᵖ ⥤ Type u}
    (α : X ⟶ X') (β : Y ⟶ Y') {n a b : AugmentedSimplexCategory} (h : a ⊗ b = n)
    (x : X.obj (op a)) (y : Y.obj (op b)) :
    (DayConvolution.map α β).app (op n) ((X ⊛ Y).map (eqToHom h.symm).op
        ((DayConvolution.unit X Y).app (op a, op b) ((x, y) : X.obj (op a) × Y.obj (op b)))) =
      (X' ⊛ Y').map (eqToHom h.symm).op ((DayConvolution.unit X' Y').app (op a, op b)
        ((α.app _ x, β.app _ y) : X'.obj (op a) × Y'.obj (op b))) := by
  rw [NatTrans.naturality_apply]
  exact congrArg _
    (ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app α β (op a) (op b))
      ((x, y) : X.obj (op a) × Y.obj (op b)))

variable (X Y : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)

private noncomputable def toSigma (n : AugmentedSimplexCategory)
    (t : Σ j : CostructuredArrow (tensor AugmentedSimplexCategoryᵒᵖ) (op n),
      (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).obj j) :
    Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory // s.1 ⊗ s.2 = n},
      X.obj (op s.1.1) × Y.obj (op s.1.2) :=
  ⟨(decomposition n t.1.left.1.unop t.1.left.2.unop t.1.hom.unop).1,
    X.map (decomposition n t.1.left.1.unop t.1.left.2.unop t.1.hom.unop).2.1.op t.2.1,
    Y.map (decomposition n t.1.left.1.unop t.1.left.2.unop t.1.hom.unop).2.2.op t.2.2⟩

private lemma toSigma_mk {n : AugmentedSimplexCategory}
    (j : CostructuredArrow (tensor AugmentedSimplexCategoryᵒᵖ) (op n))
    (z : (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).obj j)
    {s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory // s.1 ⊗ s.2 = n}}
    {g : s.1.1 ⟶ j.left.1.unop} {k : s.1.2 ⟶ j.left.2.unop}
    (hd : decomposition n j.left.1.unop j.left.2.unop j.hom.unop = ⟨s, g, k⟩) :
    toSigma X Y n ⟨j, z⟩ = ⟨s, X.map g.op z.1, Y.map k.op z.2⟩ := by
  dsimp only [toSigma]
  rw [hd]

private lemma toSigma_eq_of_rel (n : AugmentedSimplexCategory)
    {t t' : Σ j : CostructuredArrow (tensor AugmentedSimplexCategoryᵒᵖ) (op n),
      (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).obj j}
    (h : (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙
      X ⊠ Y).ColimitTypeRel t t') :
    toSigma X Y n t = toSigma X Y n t' := by
  obtain ⟨j, z⟩ := t
  obtain ⟨j', z'⟩ := t'
  obtain ⟨f, hf⟩ := h
  suffices key : ∀ (f : j ⟶ j') (z' : (CostructuredArrow.proj
      (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).obj j'),
      z' = (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).map f z →
      toSigma X Y n ⟨j, z⟩ = toSigma X Y n ⟨j', z'⟩ from key f z' hf
  rintro f z' rfl
  have hw : j.hom.unop = j'.hom.unop ≫ (f.left.1.unop ⊗ₘ f.left.2.unop) := by
    rw [← CostructuredArrow.w f]
    rfl
  generalize hq : decomposition n j'.left.1.unop j'.left.2.unop j'.hom.unop = q
  obtain ⟨⟨⟨a, b⟩, hs⟩, g, k⟩ := q
  have hq' := (Equiv.symm_apply_eq _).1 hq
  have hd : decomposition n j.left.1.unop j.left.2.unop j.hom.unop =
      ⟨⟨(a, b), hs⟩, g ≫ f.left.1.unop, k ≫ f.left.2.unop⟩ := by
    rw [← decomposition_eqToHom_comp_tensorHom, hw, hq', ← tensorHom_comp_tensorHom,
      ← Category.assoc]
    rfl
  rw [toSigma_mk X Y _ _ hd, toSigma_mk X Y _ _ hq]
  simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp]
  rfl

theorem bijective_map_unit_app (n : AugmentedSimplexCategory) :
    Function.Bijective (fun p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
        s.1 ⊗ s.2 = n}, X.obj (op s.1.1) × Y.obj (op s.1.2) ↦
      (X ⊛ Y).map (eqToHom p.1.2.symm).op
        ((DayConvolution.unit X Y).app (op p.1.1.1, op p.1.1.2) p.2)) := by
  constructor
  · rintro ⟨⟨⟨a, b⟩, h⟩, x, y⟩ ⟨⟨⟨a', b'⟩, h'⟩, x', y'⟩ he
    have he' := (DayConvolution.map_unit_app_eq_map_unit_app_iff X Y
      (x := op a) (y := op b) (x' := op a') (y' := op b') (eqToHom h.symm).op
      (eqToHom h'.symm).op x y x' y').1 he
    have key : ∀ {t t'}, Relation.EqvGen (CostructuredArrow.proj
        (tensor AugmentedSimplexCategoryᵒᵖ) (op n) ⋙ X ⊠ Y).ColimitTypeRel t t' →
        toSigma X Y n t = toSigma X Y n t' := fun h ↦ by
      induction h with
      | rel _ _ h => exact toSigma_eq_of_rel X Y n h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
    have hs : ∀ {a b : AugmentedSimplexCategory} (h : a ⊗ b = n) (x : X.obj (op a))
        (y : Y.obj (op b)), toSigma X Y n ⟨CostructuredArrow.mk (Y := (op a, op b))
          (eqToHom h.symm).op, (x, y)⟩ = ⟨⟨(a, b), h⟩, x, y⟩ := fun h x y ↦ by
      have hd := decomposition_eqToHom_comp_tensorHom h (𝟙 _) (𝟙 _)
      rw [MonoidalCategory.id_tensorHom_id, Category.comp_id] at hd
      rw [toSigma_mk X Y _ _ hd]
      simp
    rw [← hs h x y, ← hs h' x' y']
    exact key he'
  · intro t
    obtain ⟨x', y', u, a, b, rfl⟩ := DayConvolution.map_unit_app_jointly_surjective X Y t
    obtain ⟨⟨⟨s, h⟩, g, k⟩, hu⟩ := (bijective_eqToHom_comp_tensorHom n x'.unop y'.unop).2 u.unop
    refine ⟨⟨⟨s, h⟩, X.map g.op a, Y.map k.op b⟩, ?_⟩
    have hu' : u = (g.op ⊗ₘ k.op) ≫ (eqToHom h.symm).op := Quiver.Hom.unop_inj hu.symm
    have : (DayConvolution.unit X Y).app (op s.1, op s.2) (X.map g.op a, Y.map k.op b) =
        (X ⊛ Y).map (g.op ⊗ₘ k.op) ((DayConvolution.unit X Y).app (x', y') (a, b)) :=
      NatTrans.naturality_apply (DayConvolution.unit X Y) (X := (x', y'))
        (Y := (op s.1, op s.2)) (g.op, k.op) ((a, b) : X.obj x' × Y.obj y')
    dsimp only
    rw [hu', Functor.map_comp_apply]
    exact congrArg _ this

end AugmentedSimplexCategory

namespace SSet

def trivialAugmentation : SSet.{u} ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  { obj X := X.augmentOfIsTerminal Limits.Types.isTerminalPUnit
    map f := CommaMorphism.mk (X := SimplicialObject.augmentOfIsTerminal _ _)
      (Y := SimplicialObject.augmentOfIsTerminal _ _) f (𝟙 _) (by ext; rfl) } ⋙
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse

def trivialAugmentationCompIso :
    trivialAugmentation ⋙ (Functor.whiskeringLeft _ _ _).obj
      AugmentedSimplexCategory.inclusion.op ≅ 𝟭 SSet.{u} :=
  Iso.refl _

instance (X : SSet.{u}) : Unique ((trivialAugmentation.obj X).obj (op WithInitial.star)) :=
  inferInstanceAs (Unique PUnit)

noncomputable def join (X Y : SSet.{u}) : SSet.{u} :=
  AugmentedSimplexCategory.inclusion.op ⋙ (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)

noncomputable def joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    join X Y ⟶ join X' Y' :=
  Functor.whiskerLeft _ (DayConvolution.map (trivialAugmentation.map f) (trivialAugmentation.map g))

noncomputable def joinFunctor : SSet.{u} × SSet.{u} ⥤ SSet.{u} where
  obj p := join p.1 p.2
  map f := joinMap f.1 f.2
  map_id p := by
    have h : DayConvolution.map (trivialAugmentation.map (𝟙 p.1))
        (trivialAugmentation.map (𝟙 p.2)) = 𝟙 _ := by
      rw [trivialAugmentation.map_id, trivialAugmentation.map_id, DayConvolution.map_id]
    exact congrArg (Functor.whiskerLeft _) h
  map_comp f g := by
    have h : DayConvolution.map (trivialAugmentation.map (f.1 ≫ g.1))
        (trivialAugmentation.map (f.2 ≫ g.2)) = DayConvolution.map
          (trivialAugmentation.map f.1) (trivialAugmentation.map f.2) ≫ DayConvolution.map
          (trivialAugmentation.map g.1) (trivialAugmentation.map g.2) := by
      rw [trivialAugmentation.map_comp, trivialAugmentation.map_comp, DayConvolution.map_comp]
    exact congrArg (Functor.whiskerLeft _) h

@[reassoc]
theorem joinMap_comp_joinMap {X X' X'' Y Y' Y'' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    joinMap f g ≫ joinMap f' g' = joinMap (f ≫ f') (g ≫ g') :=
  (joinFunctor.map_comp (X := (X, Y)) (Y := (X', Y')) (Z := (X'', Y'')) (f, g) (f', g')).symm

theorem joinMap_comp_joinMap_id {X Y W : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (Z : SSet.{u}) :
    joinMap f (𝟙 Z) ≫ joinMap g (𝟙 Z) = joinMap (f ≫ g) (𝟙 Z) := by
  rw [joinMap_comp_joinMap, Category.comp_id]

noncomputable def joinInclLeft (X Y : SSet.{u}) : X ⟶ join X Y where
  app n := TypeCat.ofHom fun x ↦
    (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y)).app
      (op (.of n.unop), op .star)
        ((x, default) : (trivialAugmentation.obj X).obj (op (.of n.unop)) ×
          (trivialAugmentation.obj Y).obj (op .star))
  naturality n m f := by
    ext x
    refine Eq.trans ?_ (NatTrans.naturality_apply
      (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y))
      (X := (op (.of n.unop), op .star)) (Y := (op (.of m.unop), op .star))
      (AugmentedSimplexCategory.inclusion.op.map f, 𝟙 _) ((x, default) :
        (trivialAugmentation.obj X).obj (op (.of n.unop)) ×
          (trivialAugmentation.obj Y).obj (op .star)))
    rfl

noncomputable def joinInclRight (X Y : SSet.{u}) : Y ⟶ join X Y where
  app n := TypeCat.ofHom fun y ↦
    (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y)).app
      (op .star, op (.of n.unop))
        ((default, y) : (trivialAugmentation.obj X).obj (op .star) ×
          (trivialAugmentation.obj Y).obj (op (.of n.unop)))
  naturality n m f := by
    ext y
    refine Eq.trans ?_ (NatTrans.naturality_apply
      (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y))
      (X := (op .star, op (.of n.unop))) (Y := (op .star, op (.of m.unop)))
      (𝟙 _, AugmentedSimplexCategory.inclusion.op.map f) ((default, y) :
        (trivialAugmentation.obj X).obj (op .star) ×
          (trivialAugmentation.obj Y).obj (op (.of n.unop))))
    rfl

instance mono_joinInclLeft (X Y : SSet.{u}) : Mono (joinInclLeft X Y) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x x' h
  have := (AugmentedSimplexCategory.bijective_map_unit_app (trivialAugmentation.obj X)
    (trivialAugmentation.obj Y) (.of n.unop)).1
    (a₁ := ⟨⟨(.of n.unop, .star), rfl⟩, x, default⟩)
    (a₂ := ⟨⟨(.of n.unop, .star), rfl⟩, x', default⟩) (congrArg _ h)
  exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj_iff.1 this).2)

instance mono_joinInclRight (X Y : SSet.{u}) : Mono (joinInclRight X Y) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro y y' h
  have := (AugmentedSimplexCategory.bijective_map_unit_app (trivialAugmentation.obj X)
    (trivialAugmentation.obj Y) (.of n.unop)).1
    (a₁ := ⟨⟨(.star, .of n.unop), rfl⟩, default, y⟩)
    (a₂ := ⟨⟨(.star, .of n.unop), rfl⟩, default, y'⟩) (congrArg _ h)
  exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj_iff.1 this).2)

@[reassoc]
theorem joinInclLeft_comp_joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    joinInclLeft X Y ≫ joinMap f g = f ≫ joinInclLeft X' Y' := by
  ext n x
  exact (ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app (trivialAugmentation.map f)
    (trivialAugmentation.map g) (op (.of n.unop)) (op .star))
      ((x, default) : (trivialAugmentation.obj X).obj (op (.of n.unop)) ×
        (trivialAugmentation.obj Y).obj (op .star))).trans
    (congrArg _ (Prod.ext rfl (Subsingleton.elim _ _)))

@[reassoc]
theorem joinInclRight_comp_joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    joinInclRight X Y ≫ joinMap f g = g ≫ joinInclRight X' Y' := by
  ext n y
  exact (ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app (trivialAugmentation.map f)
    (trivialAugmentation.map g) (op .star) (op (.of n.unop)))
      ((default, y) : (trivialAugmentation.obj X).obj (op .star) ×
        (trivialAugmentation.obj Y).obj (op (.of n.unop)))).trans
    (congrArg _ (Prod.ext (Subsingleton.elim _ _) rfl))

private lemma injective_trivialAugmentation_map_app {X X' : SSet.{u}} (f : X ⟶ X') [Mono f]
    (c : AugmentedSimplexCategoryᵒᵖ) : Function.Injective ((trivialAugmentation.map f).app c) := by
  obtain ⟨c⟩ := c
  cases c with
  | star => exact Function.injective_of_subsingleton _
  | of c => exact (mono_iff_injective (f.app (op c))).1 inferInstance

instance mono_joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') [Mono f] [Mono g] :
    Mono (joinMap f g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  have hb := AugmentedSimplexCategory.bijective_map_unit_app (trivialAugmentation.obj X)
    (trivialAugmentation.obj Y) (.of n.unop)
  have hb' := AugmentedSimplexCategory.bijective_map_unit_app (trivialAugmentation.obj X')
    (trivialAugmentation.obj Y') (.of n.unop)
  intro t t' h
  obtain ⟨⟨s, x, y⟩, rfl⟩ := hb.2 t
  obtain ⟨⟨s', x', y'⟩, rfl⟩ := hb.2 t'
  have h' := hb'.1 (a₁ := ⟨s, (trivialAugmentation.map f).app _ x,
    (trivialAugmentation.map g).app _ y⟩) (a₂ := ⟨s', (trivialAugmentation.map f).app _ x',
    (trivialAugmentation.map g).app _ y'⟩)
    ((AugmentedSimplexCategory.map_app_map_unit_app _ _ s.2 x y).symm.trans
      (h.trans (AugmentedSimplexCategory.map_app_map_unit_app _ _ s'.2 x' y')))
  obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.1 h'
  obtain ⟨hx, hy⟩ := Prod.mk.inj (eq_of_heq h'')
  obtain rfl := injective_trivialAugmentation_map_app f _ hx
  obtain rfl := injective_trivialAugmentation_map_app g _ hy
  rfl

def stdSimplexToHom (s : SimplexCategory) :
    ∀ x : AugmentedSimplexCategory,
      (trivialAugmentation.obj (stdSimplex.obj s)).obj (op x) → (x ⟶ .of s)
  | .star, _ => WithInitial.starInitial.to _
  | .of k, a => stdSimplex.objEquiv (n := s) (m := op k) a

private lemma bijective_stdSimplexToHom (s : SimplexCategory) (x : AugmentedSimplexCategory) :
    Function.Bijective (stdSimplexToHom s x) := by
  cases x with
  | star => exact ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  | of k => exact stdSimplex.objEquiv.bijective

theorem stdSimplexToHom_map (s : SimplexCategory) {x x' : AugmentedSimplexCategoryᵒᵖ} (f : x ⟶ x')
    (a : (trivialAugmentation.obj (stdSimplex.obj s)).obj x) :
    stdSimplexToHom s x'.unop ((trivialAugmentation.obj (stdSimplex.obj s)).map f a) =
      f.unop ≫ stdSimplexToHom s x.unop a := by
  obtain ⟨x⟩ := x
  obtain ⟨x'⟩ := x'
  cases x' with
  | star => exact Subsingleton.elim _ _
  | of k' =>
    cases x with
    | star => exact (WithInitial.false_of_to_star f.unop).elim
    | of k => rfl

def stdSimplexJoinFamily (m n : ℕ) :
    { φ : ∀ x y : AugmentedSimplexCategoryᵒᵖ, (trivialAugmentation.obj Δ[m]).obj x →
        (trivialAugmentation.obj Δ[n]).obj y →
          (uliftYoneda.{u}.obj (WithInitial.of ⦋m⦌ ⊗ WithInitial.of ⦋n⦌)).obj (x ⊗ y) //
      ∀ {x x' y y' : AugmentedSimplexCategoryᵒᵖ} (f : x ⟶ x') (g : y ⟶ y')
        (a : (trivialAugmentation.obj Δ[m]).obj x) (b : (trivialAugmentation.obj Δ[n]).obj y),
        φ x' y' ((trivialAugmentation.obj Δ[m]).map f a)
            ((trivialAugmentation.obj Δ[n]).map g b) =
          (uliftYoneda.{u}.obj (WithInitial.of ⦋m⦌ ⊗ WithInitial.of ⦋n⦌)).map (f ⊗ₘ g)
            (φ x y a b) } :=
  ⟨fun x y a b ↦ ULift.up (stdSimplexToHom _ x.unop a ⊗ₘ stdSimplexToHom _ y.unop b),
    fun f g a b ↦ by
      apply ULift.ext
      exact (congrArg₂ (· ⊗ₘ ·) (stdSimplexToHom_map _ f a) (stdSimplexToHom_map _ g b)).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm⟩

private noncomputable def stdSimplexJoinHom (m n : ℕ) : join Δ[m] Δ[n] ⟶ Δ[m + n + 1] :=
  Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op
    ((DayConvolution.homEquiv _ _ _).symm (stdSimplexJoinFamily.{u} m n))

private lemma stdSimplexJoinHom_app_map_unit_app (m n : ℕ) (k : SimplexCategoryᵒᵖ)
    (p : Σ s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
      s.1 ⊗ s.2 = .of k.unop}, (trivialAugmentation.obj Δ[m]).obj (op s.1.1) ×
        (trivialAugmentation.obj Δ[n]).obj (op s.1.2)) :
    (stdSimplexJoinHom.{u} m n).app k
        ((trivialAugmentation.obj Δ[m] ⊛ trivialAugmentation.obj Δ[n]).map
          (eqToHom p.1.2.symm).op ((DayConvolution.unit (trivialAugmentation.obj Δ[m])
            (trivialAugmentation.obj Δ[n])).app (op p.1.1.1, op p.1.1.2) p.2)) =
      ULift.up (eqToHom p.1.2.symm ≫ (stdSimplexToHom _ _ p.2.1 ⊗ₘ stdSimplexToHom _ _ p.2.2)) := by
  refine (NatTrans.naturality_apply ((DayConvolution.homEquiv _ _ _).symm
    (stdSimplexJoinFamily.{u} m n)) (eqToHom p.1.2.symm).op _).trans
    ((congrArg _ (DayConvolution.homEquiv_symm_app_unit_app _ _ _ (stdSimplexJoinFamily.{u} m n)
      _ _ p.2.1 p.2.2)).trans ?_)
  rfl

private lemma bijective_stdSimplexJoinHom_app (m n : ℕ) (k : SimplexCategoryᵒᵖ) :
    Function.Bijective ((stdSimplexJoinHom.{u} m n).app k) := by
  refine (Function.Bijective.of_comp_iff _ (AugmentedSimplexCategory.bijective_map_unit_app
    (trivialAugmentation.obj Δ[m]) (trivialAugmentation.obj Δ[n]) (.of k.unop))).1 ?_
  obtain ⟨hi, hs⟩ := Equiv.ulift.symm.bijective.comp
    ((AugmentedSimplexCategory.bijective_eqToHom_comp_tensorHom _ _ _).comp
      (Equiv.sigmaCongrRight fun (s : {s : AugmentedSimplexCategory × AugmentedSimplexCategory //
          s.1 ⊗ s.2 = .of k.unop}) ↦
        (Equiv.ofBijective _ (bijective_stdSimplexToHom ⦋m⦌ s.1.1)).prodCongr
          (Equiv.ofBijective _ (bijective_stdSimplexToHom ⦋n⦌ s.1.2))).bijective)
  refine ⟨fun p q h ↦ hi ?_, fun t ↦ ?_⟩
  · exact (stdSimplexJoinHom_app_map_unit_app m n k p).symm.trans
      (h.trans (stdSimplexJoinHom_app_map_unit_app m n k q))
  · obtain ⟨p, hp⟩ := hs t
    exact ⟨p, (stdSimplexJoinHom_app_map_unit_app m n k p).trans hp⟩

noncomputable def stdSimplexJoinIso (m n : ℕ) : join Δ[m] Δ[n] ≅ Δ[m + n + 1] :=
  NatIso.ofComponents
    (fun k ↦ (Equiv.ofBijective _ (bijective_stdSimplexJoinHom_app.{u} m n k)).toIso)
    (fun f ↦ (stdSimplexJoinHom m n).naturality f)

private lemma tensorHom_starInitial_to {k x : SimplexCategory}
    (f : (WithInitial.of k : AugmentedSimplexCategory) ⟶ .of x) (y : SimplexCategory) :
    f ⊗ₘ WithInitial.starInitial.to (.of y) = f ≫ AugmentedSimplexCategory.inl (.of x) (.of y) :=
  AugmentedSimplexCategory.inl_comp_tensorHom f (WithInitial.starInitial.to (.of y))

private lemma starInitial_to_tensorHom {k y : SimplexCategory}
    (f : (WithInitial.of k : AugmentedSimplexCategory) ⟶ .of y) (x : SimplexCategory) :
    WithInitial.starInitial.to (.of x) ⊗ₘ f = f ≫ AugmentedSimplexCategory.inr (.of x) (.of y) :=
  AugmentedSimplexCategory.inr_comp_tensorHom (WithInitial.starInitial.to (.of x)) f

theorem joinInclLeft_comp_stdSimplexJoinIso_hom (m n : ℕ) :
    joinInclLeft Δ[m] Δ[n] ≫ (stdSimplexJoinIso m n).hom =
      stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) := by
  ext k x
  exact (DayConvolution.homEquiv_symm_app_unit_app _ _ _ (stdSimplexJoinFamily m n)
    (op (.of k.unop)) (op .star) x default).trans (ULift.ext _ _ (tensorHom_starInitial_to _ _))

theorem joinInclRight_comp_stdSimplexJoinIso_hom (m n : ℕ) :
    joinInclRight Δ[m] Δ[n] ≫ (stdSimplexJoinIso m n).hom =
      stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) := by
  ext k y
  exact (DayConvolution.homEquiv_symm_app_unit_app _ _ _ (stdSimplexJoinFamily m n)
    (op .star) (op (.of k.unop)) default y).trans (ULift.ext _ _ (starInitial_to_tensorHom _ _))

private theorem stdSimplexJoinIso_hom_app_unit (m n : ℕ) :
    (stdSimplexJoinIso.{u} m n).hom.app (op ⦋m + n + 1⦌)
      ((DayConvolution.unit (trivialAugmentation.obj (Δ[m] : SSet.{u}))
        (trivialAugmentation.obj (Δ[n] : SSet.{u}))).app
        (op (.of ⦋m⦌), op (.of ⦋n⦌)) (yonedaEquiv (𝟙 Δ[m]), yonedaEquiv (𝟙 Δ[n]))) =
      yonedaEquiv (𝟙 (Δ[m + n + 1] : SSet.{u})) := by
  refine (DayConvolution.homEquiv_symm_app_unit_app _ _ _ (stdSimplexJoinFamily.{u} m n)
    (op (.of ⦋m⦌)) (op (.of ⦋n⦌)) (yonedaEquiv (𝟙 (Δ[m] : SSet.{u})))
    (yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))).trans (ULift.ext _ _ ?_)
  exact (congrArg₂ (· ⊗ₘ ·) (rfl : _ = 𝟙 (WithInitial.of ⦋m⦌))
    (rfl : _ = 𝟙 (WithInitial.of ⦋n⦌))).trans (id_tensorHom_id _ _)

@[reassoc]
theorem joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom {k k' m m' : ℕ}
    (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋k'⦌ ⟶ ⦋m'⦌) :
    joinMap (stdSimplex.map f) (stdSimplex.map g) ≫ (stdSimplexJoinIso.{u} m m').hom =
      (stdSimplexJoinIso k k').hom ≫ stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f g) := by
  rw [← Iso.inv_comp_eq]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  have hu : yonedaEquiv (stdSimplexJoinIso.{u} k k').inv =
      (DayConvolution.unit (trivialAugmentation.obj (Δ[k] : SSet.{u}))
        (trivialAugmentation.obj (Δ[k'] : SSet.{u}))).app
        (op (.of ⦋k⦌), op (.of ⦋k'⦌)) (yonedaEquiv (𝟙 Δ[k]), yonedaEquiv (𝟙 Δ[k'])) := by
    rw [← (Category.id_comp (stdSimplexJoinIso.{u} k k').inv), yonedaEquiv_comp,
      ← stdSimplexJoinIso_hom_app_unit k k']
    exact ConcreteCategory.congr_hom (congr_app (stdSimplexJoinIso.{u} k k').hom_inv_id _) _
  rw [hu]
  have hj := ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (trivialAugmentation.map (stdSimplex.map f)) (trivialAugmentation.map (stdSimplex.map g))
    (op (.of ⦋k⦌)) (op (.of ⦋k'⦌)))
    ((yonedaEquiv (𝟙 (Δ[k] : SSet.{u})), yonedaEquiv (𝟙 (Δ[k'] : SSet.{u}))) :
      (trivialAugmentation.obj (Δ[k] : SSet.{u})).obj (op (.of ⦋k⦌)) ×
        (trivialAugmentation.obj (Δ[k'] : SSet.{u})).obj (op (.of ⦋k'⦌)))
  refine (congrArg ((stdSimplexJoinIso.{u} m m').hom.app _) hj).trans ?_
  exact DayConvolution.homEquiv_symm_app_unit_app _ _ _ (stdSimplexJoinFamily.{u} m m')
    (op (.of ⦋k⦌)) (op (.of ⦋k'⦌)) _ _

end SSet
