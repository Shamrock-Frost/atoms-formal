import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Atoms.Homotopical.Simplicial.Cartesian

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace Atoms.Homotopical

section Cartesian

open MarkedSSet.modelCategoryCartesian

theorem weakEquivalence_of_isIso_forget_map {A B : MarkedSSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (F : SSet.{u}) [F.Quasicategory] (g : MarkedPresheaf.forget.obj B ⟶ F),
      (∀ e ∈ A.marked ⦋1⦌,
        Nonempty (SSet.Edge.mk' ((MarkedPresheaf.forget.map i ≫ g).app _ e)).InvStruct) →
      ∀ e ∈ B.marked ⦋1⦌, Nonempty (SSet.Edge.mk' (g.app _ e)).InvStruct) :
    WeakEquivalence i := by
  refine weakEquivalence_of_hasLiftingProperty i fun X Y p hX _ _ ↦ ⟨fun {u v} sq ↦ ?_⟩
  obtain ⟨hXq, hXn⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff X).1 hX
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) := hXq
  let l : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj X :=
    inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map u
  have hl : MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u :=
    IsIso.hom_inv_id_assoc _ _
  refine ⟨⟨⟨edgeHomMk l fun e he ↦ (hXn _).2 (h _ l (fun e' he' ↦ ?_) e he),
    MarkedPresheaf.hom_ext ?_, MarkedPresheaf.hom_ext ?_⟩⟩⟩
  · rw [hl]
    exact (hXn _).1 (MarkedPresheaf.map_mem_marked u he')
  · exact (Functor.map_comp _ _ _).trans hl
  · have hp : l ≫ MarkedPresheaf.forget.map p = MarkedPresheaf.forget.map v := by
      rw [Category.assoc, ← Functor.map_comp, sq.w, Functor.map_comp, IsIso.inv_hom_id_assoc]
    exact (Functor.map_comp _ _ _).trans hp

private theorem weakEquivalence_counit (X : MarkedSSet.{u}) [hX : IsFibrant X] :
    WeakEquivalence ((MarkedPresheaf.flatForgetAdjunction edgeMarking).counit.app X) := by
  have : IsIso (MarkedPresheaf.forget.map
      ((MarkedPresheaf.flatForgetAdjunction edgeMarking).counit.app X)) :=
    inferInstanceAs (IsIso (𝟙 _))
  obtain ⟨-, hXn⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff X).1 hX
  refine weakEquivalence_of_isIso_forget_map _ fun F _ g _ e he ↦ ?_
  obtain ⟨I⟩ := (hXn e).1 he
  exact ⟨(I.map g).ofEq rfl⟩

private noncomputable def flatCylinderComparison (Y : SSet.{u}) :
    (MarkedPresheaf.flat edgeMarking).obj (joyalInterval.{u}.cylinder.I.obj Y) ⟶
      cartesianCylinder.{u}.I.obj ((MarkedPresheaf.flat edgeMarking).obj Y) :=
  ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm
    (cartesianCylinderForgetIso.app ((MarkedPresheaf.flat edgeMarking).obj Y)).inv

private theorem weakEquivalence_flatCylinderComparison (Y : SSet.{u}) :
    WeakEquivalence (flatCylinderComparison Y) := by
  have : IsIso (MarkedPresheaf.forget.map (flatCylinderComparison Y)) :=
    inferInstanceAs (IsIso (cartesianCylinderForgetIso.app
      ((MarkedPresheaf.flat edgeMarking).obj Y)).inv)
  refine weakEquivalence_of_isIso_forget_map _ fun F _ g _ e he ↦ ?_
  have hb : (MarkedPresheaf.forget.map prod.snd).app _ e ∈
      ((MarkedPresheaf.flat edgeMarking).obj Y).marked ⦋1⦌ :=
    MarkedPresheaf.map_mem_marked (prod.snd : MarkedSSet.sharpJ ⨯ _ ⟶ _) he
  obtain ⟨y, hy⟩ := exists_eq_σ_of_mem_marked_flat _ hb
  have key := nonempty_invStruct_app_prod_σ
    (MarkedPresheaf.forget.map (flatCylinderComparison Y) ≫ g)
    ((MarkedPresheaf.forget.map prod.fst).app _ e) y
  have he' : (MarkedPresheaf.forget.map (flatCylinderComparison Y)).app _
      ((MarkedPresheaf.forget.map prod.fst).app _ e, Y.σ 0 y) = e := by
    rw [← hy]
    exact ConcreteCategory.congr_hom (congr_app (cartesianCylinderForgetIso.app _).hom_inv_id _) e
  rw [← he']
  exact key

private theorem weakEquivalence_flat_map_contraction (Y : SSet.{u}) :
    WeakEquivalence ((MarkedPresheaf.flat edgeMarking).map
      (joyalInterval.{u}.cylinder.contraction.app Y)) := by
  have := weakEquivalence_flatCylinderComparison Y
  let X := (MarkedPresheaf.flat edgeMarking).obj Y
  have : WeakEquivalence ((cartesianCylinder.{u}.endpoint false).app X) :=
    (weakEquivalence_iff _).2 (cartesianCylinder.{u}.anodyne_le_weakEquivalences _
      cartesianGenerators_le_monomorphisms _ (cartesianCylinder.{u}.anodyne_endpoint _ false X))
  have : WeakEquivalence (𝟙 X) := inferInstance
  have : WeakEquivalence (cartesianCylinder.{u}.contraction.app X) :=
    weakEquivalence_of_precomp_of_fac (cartesianCylinder.{u}.endpoint_app_contraction_app false X)
  have h : (MarkedPresheaf.flat edgeMarking).map (joyalInterval.{u}.cylinder.contraction.app Y) =
      flatCylinderComparison Y ≫ cartesianCylinder.{u}.contraction.app X := by
    refine MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans ?_).symm
    refine (Iso.inv_comp_eq (cartesianCylinderForgetIso.app X)).2 ?_
    exact (congr_app cartesianCylinderForgetIso_hom_comp_whiskerLeft_contraction X).symm
  rw [h]
  infer_instance

theorem weakEquivalence_ofEdgeSetHom_id {Z : SSet.{u}} {E E' : Set (Z _⦋1⦌)} (hEE' : E ⊆ E')
    (h : ∀ (F : SSet.{u}) [F.Quasicategory] (g : Z ⟶ F),
      (∀ e ∈ E, Nonempty (SSet.Edge.mk' (g.app _ e)).InvStruct) →
        ∀ e ∈ E', Nonempty (SSet.Edge.mk' (g.app _ e)).InvStruct) :
    WeakEquivalence (MarkedSSet.ofEdgeSetHom (𝟙 Z) E E' fun _ he => hEE' he) := by
  have : IsIso (MarkedPresheaf.forget.map
      (MarkedSSet.ofEdgeSetHom (𝟙 Z) E E' fun _ he => hEE' he)) := inferInstanceAs (IsIso (𝟙 Z))
  refine weakEquivalence_of_isIso_forget_map _ fun F _ g hg e he ↦ ?_
  rcases (MarkedSSet.mem_marked_ofEdgeSet Z E' e).1 he with he | ⟨x, rfl⟩
  · exact h F g (fun e' he' ↦ hg e' ((MarkedSSet.mem_marked_ofEdgeSet Z E e').2 (Or.inl he')))
      e he
  · exact ⟨(SSet.Edge.InvStruct.invStructId (g.app _ x)).ofEq
      (SSet.σ_naturality_apply g 0 x).symm⟩

private theorem weakEquivalence_ofEdgeSetHom_of_hasLift {K L : SSet.{u}} (j : K ⟶ L)
    (E : Set (K _⦋1⦌)) (E' : Set (L _⦋1⦌)) (hE : ∀ e ∈ E, j.app _ e ∈ E')
    (hE' : ∀ e ∈ E', ∃ e₀ ∈ E, j.app _ e₀ = e)
    (hlift : ∀ {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.InnerFibration p] [X.Quasicategory]
      [Y.Quasicategory] {a : K ⟶ X} {b : L ⟶ Y} (sq : CommSq a j p b),
      (∀ e ∈ E, Nonempty (SSet.Edge.mk' (a.app _ e)).InvStruct) → sq.HasLift) :
    WeakEquivalence (MarkedSSet.ofEdgeSetHom j E E' hE) := by
  refine weakEquivalence_of_hasLiftingProperty _ fun X Y p hX hY hp ↦ ⟨fun {u v} sq ↦ ?_⟩
  obtain ⟨hXq, hXn⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff X).1 hX
  obtain ⟨hYq, -⟩ := (MarkedSSet.modelCategoryCartesian.isFibrant_iff Y).1 hY
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) := hXq
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj Y) := hYq
  have : SSet.Isofibration (MarkedPresheaf.forget.map p) :=
    (MarkedSSet.modelCategoryCartesian.fibration_iff_isofibration p).1 hp
  have sq' : CommSq (MarkedPresheaf.forget.map u) j (MarkedPresheaf.forget.map p)
      (MarkedPresheaf.forget.map v) :=
    ⟨(Functor.map_comp _ _ _).symm.trans ((congrArg MarkedPresheaf.forget.map sq.w).trans
      (Functor.map_comp _ _ _))⟩
  obtain ⟨l⟩ := (hlift _ sq' fun e he ↦ (hXn _).1 (MarkedPresheaf.map_mem_marked u
    ((MarkedSSet.mem_marked_ofEdgeSet K E e).2 (Or.inl he)))).exists_lift
  refine ⟨⟨⟨edgeHomMk l.l fun e he ↦ ?_, MarkedPresheaf.hom_ext ?_,
    MarkedPresheaf.hom_ext ?_⟩⟩⟩
  · rcases (MarkedSSet.mem_marked_ofEdgeSet L E' e).1 he with he | ⟨x, rfl⟩
    · obtain ⟨e₀, he₀, rfl⟩ := hE' e he
      have h₁ : l.l.app _ (j.app _ e₀) = (MarkedPresheaf.forget.map u).app _ e₀ :=
        ConcreteCategory.congr_hom (congr_app l.fac_left _) e₀
      exact h₁ ▸ MarkedPresheaf.map_mem_marked u
        ((MarkedSSet.mem_marked_ofEdgeSet K E e₀).2 (Or.inl he₀))
    · exact (SSet.σ_naturality_apply l.l 0 x).symm ▸ X.map_σ_mem_marked _
  · exact (Functor.map_comp _ _ _).trans l.fac_left
  · exact (Functor.map_comp _ _ _).trans l.fac_right

theorem weakEquivalence_ofEdgeSetHom_horn_zero (n : ℕ) :
    WeakEquivalence (MarkedSSet.ofEdgeSetHom Λ[n + 2, 0].ι
      {SSet.horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)}
      {Λ[n + 2, 0].ι.app _ (SSet.horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp))}
      (by simp)) :=
  weakEquivalence_ofEdgeSetHom_of_hasLift _ _ _ _ (fun _ he ↦ ⟨_, rfl, he.symm⟩)
    fun p _ _ _ _ _ sq h ↦ SSet.hasLift_horn_zero_of_invStruct p sq (h _ rfl)

theorem weakEquivalence_ofEdgeSetHom_horn_last (n : ℕ) :
    WeakEquivalence (MarkedSSet.ofEdgeSetHom Λ[n + 2, Fin.last (n + 2)].ι
      {SSet.horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp)}
      {Λ[n + 2, Fin.last (n + 2)].ι.app _ (SSet.horn.edge (n + 2) (Fin.last (n + 2))
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp))}
      (by simp)) :=
  weakEquivalence_ofEdgeSetHom_of_hasLift _ _ _ _ (fun _ he ↦ ⟨_, rfl, he.symm⟩)
    fun p _ _ _ _ _ sq h ↦ SSet.hasLift_horn_last_of_invStruct p sq (h _ rfl)

end Cartesian

section Quillen

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

private theorem joyalIsFibrant_iff (Z : SSet.{u}) :
    IsFibrant Z ↔ joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions Z :=
  ExactCylinder.modelCategory.isFibrant_iff joyalInterval.{u}.cylinder SSet.innerHornInclusions
    SSet.innerHornInclusions_le_monomorphisms Z

private theorem isFibrant_forget_obj (W : MarkedSSet.{u}) [hW : IsFibrant W] :
    IsFibrant (MarkedPresheaf.forget.obj W) :=
  (isFibrant_iff_quasicategory _).2
    ((MarkedSSet.modelCategoryCartesian.isFibrant_iff W).1 hW).1

private noncomputable def homotopyClassesEquiv (Y : SSet.{u}) (W : MarkedSSet.{u}) [IsFibrant W] :
    cartesianCylinder.{u}.HomotopyClasses ((MarkedPresheaf.flat edgeMarking).obj Y) W ≃
      joyalInterval.{u}.cylinder.HomotopyClasses Y (MarkedPresheaf.forget.obj W) :=
  Quotient.congr ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv Y W) fun u v ↦
    (ExactCylinder.homotopic_homEquiv_iff joyalInterval.{u}.cylinder cartesianCylinder.{u}
      SSet.innerHornInclusions cartesianGenerators (MarkedPresheaf.flatForgetAdjunction edgeMarking)
      ((weakEquivalence_iff _).1 (weakEquivalence_flat_map_contraction Y))
      ((isFibrant_iff_isFibrant W).1 inferInstance)
      ((joyalIsFibrant_iff _).1 (isFibrant_forget_obj W)) u v).symm

private theorem homotopyClassesEquiv_comp_precompClasses {A B : SSet.{u}} (f : A ⟶ B)
    (W : MarkedSSet.{u}) [IsFibrant W] :
    homotopyClassesEquiv A W ∘
        cartesianCylinder.{u}.precompClasses ((MarkedPresheaf.flat edgeMarking).map f) W =
      joyalInterval.{u}.cylinder.precompClasses f (MarkedPresheaf.forget.obj W) ∘
        homotopyClassesEquiv B W := by
  funext c
  induction c using Quotient.inductionOn with | h u => ?_
  exact congrArg (Quotient.mk _)
    ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv_naturality_left f u)

theorem weakEquivalence_flat_map_iff {A B : SSet.{u}} (f : A ⟶ B) :
    WeakEquivalence ((MarkedPresheaf.flat edgeMarking).map f) ↔ WeakEquivalence f := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  constructor
  · intro h Z hZ
    have : SSet.Quasicategory Z := (isFibrant_iff_quasicategory Z).1 ((joyalIsFibrant_iff Z).2 hZ)
    have := isFibrant_natural Z
    have hc := h (MarkedSSet.natural Z) ((isFibrant_iff_isFibrant _).1 inferInstance)
    have he := homotopyClassesEquiv_comp_precompClasses f (MarkedSSet.natural Z)
    have hc' := (homotopyClassesEquiv A _).bijective.comp hc
    rw [he] at hc'
    exact (Function.Bijective.of_comp_iff _ (homotopyClassesEquiv B _).bijective).1 hc'
  · intro h W hW
    have : IsFibrant W := (isFibrant_iff_isFibrant W).2 hW
    rw [← (homotopyClassesEquiv A W).bijective.of_comp_iff',
      homotopyClassesEquiv_comp_precompClasses]
    exact (h _ ((joyalIsFibrant_iff _).1 (isFibrant_forget_obj W))).comp
      (homotopyClassesEquiv B W).bijective

theorem isQuillenEquivalence_flatForgetAdjunction :
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).IsQuillenEquivalence := by
  have hQ : (MarkedPresheaf.flatForgetAdjunction edgeMarking).IsQuillen :=
    Adjunction.isQuillen_of_fibrations_between_fibrant _
      (fun _ _ f (_ : Mono f) ↦ (MarkedPresheaf.flat edgeMarking).map_mono f)
      fun X Y p hX hY hp ↦ by
        have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) :=
          ((MarkedSSet.modelCategoryCartesian.isFibrant_iff X).1 hX).1
        have : SSet.Quasicategory (MarkedPresheaf.forget.obj Y) :=
          ((MarkedSSet.modelCategoryCartesian.isFibrant_iff Y).1 hY).1
        exact (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
          ((MarkedSSet.modelCategoryCartesian.fibration_iff_isofibration p).1 hp)
  refine hQ.isQuillenEquivalence_iff.2 ⟨fun f hf ↦ (weakEquivalence_flat_map_iff f).1 hf,
    fun X _ B _ q _ _ ↦ ?_⟩
  have := (weakEquivalence_flat_map_iff q).2 inferInstance
  have := weakEquivalence_counit X
  infer_instance

end Quillen

end Atoms.Homotopical
