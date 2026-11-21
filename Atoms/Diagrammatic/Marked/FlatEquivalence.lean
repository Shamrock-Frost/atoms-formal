import Atoms.Diagrammatic.Marked.Fibrancy
import Atoms.Diagrammatic.Marked.FlatQuillen
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem weakEquivalence_of_isIso_forget_map (n : ℕ∞) {A B : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (Z : DiagSet.{u}), IsInftyCategory n Z → ∀ g : MarkedPresheaf.forget.obj B ⟶ Z,
      (∀ (U : Atom) (x : diagram A.underlying U), x ∈ A.marked U →
        IsEquivalence Z ((MarkedPresheaf.forget.map i ≫ g).app _ x)) →
      ∀ (U : Atom) (x : diagram B.underlying U), x ∈ B.marked U → IsEquivalence Z (g.app _ x)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map i) := by
  have key {X Y : MarkedDiagSet.{u}} (p : X ⟶ Y) (hXc : IsInftyCategory n X.underlying)
      (hXn : ∀ (U : Atom) (x : diagram X.underlying U),
        x ∈ X.marked U ↔ IsEquivalence X.underlying x) : HasLiftingProperty i p := by
    refine ⟨fun {u v} sq ↦ ?_⟩
    let l : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj X :=
      inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map u
    have hl : MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u :=
      IsIso.hom_inv_id_assoc _ _
    refine ⟨⟨⟨MarkedPresheaf.homMk l fun U x hx ↦
      (hXn U _).2 (h _ hXc l (fun U' x' hx' ↦ ?_) U x hx),
      MarkedPresheaf.hom_ext ?_, MarkedPresheaf.hom_ext ?_⟩⟩⟩
    · have e : (MarkedPresheaf.forget.map i ≫ l).app _ x' =
          (MarkedPresheaf.forget.map u).app _ x' :=
        ConcreteCategory.congr_hom (congr_app hl _) x'
      exact e ▸ (hXn U' _).1 (MarkedPresheaf.map_mem_marked u hx')
    · exact (Functor.map_comp _ _ _).trans hl
    · have hp : l ≫ MarkedPresheaf.forget.map p = MarkedPresheaf.forget.map v := by
        rw [Category.assoc, ← Functor.map_comp, sq.w, Functor.map_comp, IsIso.inv_hom_id_assoc]
      exact (Functor.map_comp _ _ _).trans hp
  refine HomotopicalAlgebra.weakEquivalence_of_hasLiftingProperty _ fun X _ p hX _ _ ↦ ?_
  obtain ⟨hXc, hXn⟩ := (isFibrant_coinductive_iff_natural n X).1 hX
  exact key p hXc hXn

theorem weakEquivalence_counit_app (n : ℕ∞) (X : MarkedDiagSet.Coinductive.{u} n)
    (hX : IsFibrant X) :
    WeakEquivalence ((DiagSet.Infty.flatForgetAdjunction n).counit.app X) := by
  let ε := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app (X : MarkedDiagSet.{u})
  have : IsIso (MarkedPresheaf.forget.map ε) := inferInstanceAs (IsIso (𝟙 _))
  obtain ⟨-, hXn⟩ := (isFibrant_coinductive_iff_natural n X).1 hX
  exact weakEquivalence_of_isIso_forget_map n ε fun _ _ g _ U x hx ↦
    IsEquivalence.map g ((hXn U x).1 hx)

theorem isFibrant_infty_iff (n : ℕ∞) (X : DiagSet.Infty.{u} n) :
    IsFibrant X ↔ IsInftyCategory n X := by
  refine ⟨isInftyCategory_of_isFibrant n X, fun hX => ?_⟩
  exact (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators n)
    (inftyGenerators_le_monomorphisms n) X).2
    (isFibrant_forget_obj n _ (isFibrant_coinductive_natural n hX))

theorem isInftyCategory_of_iso {n : ℕ∞} {Y Z : DiagSet.{u}} (e : Y ≅ Z)
    (hZ : IsInftyCategory n Z) : IsInftyCategory n Y := by
  have := (isFibrant_infty_iff n ((DiagSet.toInfty n).obj Z)).2 hZ
  exact (isFibrant_infty_iff n ((DiagSet.toInfty n).obj Y)).1
    (isFibrant_of_fibration ((DiagSet.toInfty n).map e.hom))

theorem toLoc_comp_flatCompLocIso_hom_app (Y : DiagSet.{u}) :
    toLoc ((MarkedPresheaf.flat atomMarking).obj Y) ≫ flatCompLocIso.hom.app Y = 𝟙 Y :=
  flatCompLocIso.inv_hom_id_app Y

theorem weakEquivalence_flat_map_contraction (n : ℕ∞) (Y : DiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      ((MarkedPresheaf.flat atomMarking).map (reversibleCylinder.{u}.contraction.app Y))) := by
  let F := MarkedDiagSet.toCoinductive n
  let Z := (MarkedPresheaf.flat atomMarking).obj Y
  let M := markedCylinder.obj Z
  let κ : M ⟶ Z := markedExactCylinder.{u}.contraction.app Z
  let c : Loc.obj M ⟶ Y := reversibleCylinder.{u}.contraction.app Y
  have hc : c = Loc.map κ ≫ flatCompLocIso.hom.app Y := rfl
  have hw : (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app M ≫ κ =
      (MarkedPresheaf.flat atomMarking).map (toLoc M) ≫
        (MarkedPresheaf.flat atomMarking).map c := by
    refine MarkedPresheaf.hom_ext ?_
    refine (Functor.map_comp _ _ _).trans (((congrArg (· ≫ MarkedPresheaf.forget.map κ)
      (MarkedDiagSet.forget_map_counit_app M)).trans (Category.id_comp _)).trans ?_)
    refine Eq.trans ?_ (Functor.map_comp _ _ _).symm
    change MarkedPresheaf.forget.map κ = toLoc M ≫ c
    rw [hc, toLoc_naturality_assoc]
    exact ((congrArg (MarkedPresheaf.forget.map κ ≫ ·)
      (toLoc_comp_flatCompLocIso_hom_app Y)).trans (Category.comp_id _)).symm
  let d : MarkedDiagSet.markedLoc M ⟶ Z :=
    pushout.desc κ ((MarkedPresheaf.flat atomMarking).map c) hw
  have hend : weakEquivalences (MarkedDiagSet.Coinductive n)
      (F.map ((markedExactCylinder.{u}.endpoint false).app Z)) :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _
      (coinductiveGenerators_le_monomorphisms n) _
      (markedExactCylinder.{u}.anodyne_endpoint _ false Z)
  have hκ : weakEquivalences (MarkedDiagSet.Coinductive n) (F.map κ) :=
    (weakEquivalences _).of_precomp _ _ hend
      ((congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f)
        (markedExactCylinder.{u}.endpoint_app_contraction_app false Z)).mpr
          ((weakEquivalences _).id_mem _))
  have hφ := (weakEquivalence_iff _).1 (weakEquivalence_pushout_inl_markedLoc n M)
  have hψ := (weakEquivalence_iff _).1 (weakEquivalence_pushout_inr_markedLoc n M)
  have hd : weakEquivalences (MarkedDiagSet.Coinductive n) (F.map d) :=
    (weakEquivalences _).of_precomp _ _ hφ
      ((congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f)
        (pushout.inl_desc _ _ hw)).mpr hκ)
  exact (weakEquivalence_iff _).2
    ((congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f)
      (pushout.inr_desc _ _ hw)).mp ((weakEquivalences _).comp_mem _ _ hψ hd))

noncomputable def homotopyClassesFlatEquiv (n : ℕ∞) (Y : DiagSet.{u})
    (W : MarkedDiagSet.Coinductive.{u} n) (hW : IsFibrant W) :
    markedExactCylinder.{u}.HomotopyClasses ((MarkedPresheaf.flat atomMarking).obj Y) W ≃
      reversibleCylinder.{u}.HomotopyClasses Y (MarkedPresheaf.forget.obj W) :=
  Quotient.congr ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv Y W) fun u v ↦
    (ExactCylinder.homotopic_homEquiv_iff reversibleCylinder markedExactCylinder
      (inftyGenerators n) (coinductiveGenerators n)
      (MarkedPresheaf.flatForgetAdjunction atomMarking)
      ((weakEquivalence_iff _).1 (weakEquivalence_flat_map_contraction n Y))
      ((isFibrant_coinductive_iff_isFibrant n W).1 hW) (isFibrant_forget_obj n W hW) u v).symm

theorem homotopyClassesFlatEquiv_comp_precompClasses (n : ℕ∞) {A B : DiagSet.{u}} (f : A ⟶ B)
    (W : MarkedDiagSet.Coinductive.{u} n) (hW : IsFibrant W) :
    homotopyClassesFlatEquiv n A W hW ∘
        markedExactCylinder.{u}.precompClasses ((MarkedPresheaf.flat atomMarking).map f) W =
      reversibleCylinder.{u}.precompClasses f (MarkedPresheaf.forget.obj W) ∘
        homotopyClassesFlatEquiv n B W hW := by
  funext c
  induction c using Quotient.inductionOn with | h u => ?_
  exact congrArg (Quotient.mk _)
    ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv_naturality_left f u)

theorem weakEquivalence_flat_map_iff (n : ℕ∞) {X Y : DiagSet.Infty.{u} n} (f : X ⟶ Y) :
    WeakEquivalence ((DiagSet.Infty.flat n).map f) ↔ WeakEquivalence f := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  constructor
  · intro h Z hZ
    have hZc : IsInftyCategory n Z := isInftyCategory_of_isFibrant n Z
      ((ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators n)
        (inftyGenerators_le_monomorphisms n) Z).2 hZ)
    have hN := isFibrant_coinductive_natural n hZc
    have hc := h (MarkedDiagSet.natural.obj Z) ((isFibrant_coinductive_iff_isFibrant n _).1 hN)
    have he := homotopyClassesFlatEquiv_comp_precompClasses n f _ hN
    have hc' := (congrArg Function.Bijective he).mp
      ((homotopyClassesFlatEquiv n X _ hN).bijective.comp hc)
    exact (Function.Bijective.of_comp_iff _ (homotopyClassesFlatEquiv n Y _ hN).bijective).1 hc'
  · intro h W hW
    have hW' := (isFibrant_coinductive_iff_isFibrant n W).2 hW
    refine ((homotopyClassesFlatEquiv n X W hW').bijective.of_comp_iff' _).1 ?_
    exact (congrArg Function.Bijective (homotopyClassesFlatEquiv_comp_precompClasses n f W hW')).mpr
      ((h _ (isFibrant_forget_obj n W hW')).comp (homotopyClassesFlatEquiv n Y W hW').bijective)

theorem isQuillenEquivalence_flatForgetAdjunction (n : ℕ∞) :
    (DiagSet.Infty.flatForgetAdjunction.{u} n).IsQuillenEquivalence := by
  refine (isQuillen_flatForgetAdjunction n).isQuillenEquivalence_iff.2
    ⟨fun f hf ↦ (weakEquivalence_flat_map_iff n f).1 hf, fun X hX B _ q _ _ ↦ ?_⟩
  have := (weakEquivalence_flat_map_iff n q).2 inferInstance
  have := weakEquivalence_counit_app n X hX
  infer_instance

end Atoms.Diagrammatic
