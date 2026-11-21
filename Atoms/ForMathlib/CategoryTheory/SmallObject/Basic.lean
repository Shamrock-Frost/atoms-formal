import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type

namespace CategoryTheory

open Limits

universe w v u

variable {C : Type u} [Category.{v} C]

theorem isPushout_colimMap_of_isIso {J : Type*} {P Q : Discrete J ⥤ C} [HasColimit P]
    [HasColimit Q] (α : P ⟶ Q) (k : J) (hα : ∀ j, j ≠ k → IsIso (α.app ⟨j⟩)) :
    IsPushout (colimit.ι P ⟨k⟩) (α.app ⟨k⟩) (colimMap α) (colimit.ι Q ⟨k⟩) := by
  classical
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (by simp))
    (PushoutCocone.IsColimit.mk _
      (fun s ↦ colimit.desc Q (Cocone.mk s.pt (Discrete.natTrans fun j ↦
        if h : j.as = k then eqToHom (congrArg (fun x ↦ Q.obj ⟨x⟩) h) ≫ s.inr else
          haveI := hα j.as h; inv (α.app j) ≫ colimit.ι P j ≫ s.inl))) ?_ ?_ ?_)
  · intro s
    refine colimit.hom_ext fun ⟨j⟩ ↦ ?_
    by_cases h : j = k
    · subst h
      simp [s.condition]
    · have := hα j h
      simp [h]
  · intro s
    simp
  · intro s (m : colimit Q ⟶ s.pt) (h₁ : colimMap α ≫ m = s.inl)
      (h₂ : colimit.ι Q ⟨k⟩ ≫ m = s.inr)
    apply colimit.hom_ext
    rintro ⟨j⟩
    by_cases h : j = k
    · subst h
      simp [h₂]
    · have := hα j h
      simp only [colimit.ι_desc, Discrete.natTrans_app, h, dite_false]
      rw [← h₁, ι_colimMap_assoc, IsIso.inv_hom_id_assoc]

theorem isWellOrderContinuous_monotone_functor_comp {J K : Type*} [LinearOrder J] [Preorder K]
    {φ : J → K} (hφ : Monotone φ) (D : K ⥤ C)
    (h : ∀ m, Order.IsSuccLimit m → ∀ y ≤ φ m, ∃ x < m, y ≤ φ x) :
    (hφ.functor ⋙ D).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    let ψ : Set.Iio m → Set.Iic (φ m) := fun x ↦ ⟨φ x, hφ x.2.le⟩
    have hψ : Monotone ψ := fun _ _ hxy ↦ hφ hxy
    have : hψ.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := h m hm y hy
      exact ⟨⟨x, hx⟩, hxy⟩
    let D' := (Subtype.mono_coe (· ∈ Set.Iic (φ m))).functor ⋙ D
    exact ⟨(Functor.Final.isColimitWhiskerEquiv hψ.functor
      (coconeOfDiagramTerminal isTerminalTop D')).2 (colimitOfDiagramTerminal isTerminalTop D')⟩

namespace MorphismProperty

section Coproducts

theorem sigmaMap_mem_of_wellFoundedLT {J : Type w} [LinearOrder J] [WellFoundedLT J]
    [Nonempty J] (W : MorphismProperty C) [IsCellularlyClosed.{w} W] [HasCoproducts.{w} C]
    {X₁ X₂ : J → C} (f : ∀ j, X₁ j ⟶ X₂ j) (hf : ∀ j, W (f j)) : W (Limits.Sigma.map f) := by
  classical
  let : OrderBot J := WellFoundedLT.toOrderBot J
  let : SuccOrder (WithTop J) := SuccOrder.ofLinearWellFoundedLT _
  let φ : J → WithTop J → Fin 2 := fun j i ↦ if (j : WithTop J) < i then 1 else 0
  have hφ : ∀ j, Monotone (φ j) := by
    intro j a b hab
    dsimp only [φ]
    split_ifs with h₁ h₂
    · exact le_rfl
    · exact absurd (h₁.trans_le hab) h₂
    · exact Fin.zero_le _
    · exact le_rfl
  let G : WithTop J ⥤ Discrete J ⥤ C :=
    (Discrete.functor fun j ↦ (hφ j).functor ⋙ ComposableArrows.mk₁ (f j)).flip
  have hstep : ∀ j, ((hφ j).functor ⋙ ComposableArrows.mk₁ (f j)).IsWellOrderContinuous :=
    fun j ↦ isWellOrderContinuous_monotone_functor_comp (hφ j) _ (by
      intro m hm y hy
      by_cases hj : (j : WithTop J) < m
      · have hs : (j : WithTop J) < Order.succ (j : WithTop J) :=
          Order.lt_succ_of_not_isMax (not_isMax_of_lt hj)
        refine ⟨Order.succ (j : WithTop J), hm.succ_lt hj, ?_⟩
        simp only [φ, if_pos hs]
        exact Fin.le_last y
      · refine ⟨⊥, hm.bot_lt, ?_⟩
        simpa [φ, hj] using hy)
  have hG : G.IsWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨evaluationJointlyReflectsColimits _ fun j ↦
      (haveI := hstep j.as; Functor.isColimitOfIsWellOrderContinuous
        ((hφ j.as).functor ⋙ ComposableArrows.mk₁ (f j.as)) m hm)⟩⟩
  have : PreservesWellOrderContinuousOfShape (WithTop J) (colim : (Discrete J ⥤ C) ⥤ C) :=
    ⟨fun _ _ ↦ by
      have : PreservesColimitsOfSize.{w, w} (colim : (Discrete J ⥤ C) ⥤ C) :=
        colimConstAdj.leftAdjoint_preservesColimits
      infer_instance⟩
  let F := G ⋙ colim
  let c : W.TransfiniteCompositionOfShape (WithTop J) (F.map (homOfLE bot_le : ⊥ ⟶ ⊤)) :=
    { F := F
      isoBot := Iso.refl _
      incl :=
        { app i := F.map (homOfLE le_top)
          naturality i i' g := by
            dsimp
            rw [← Functor.map_comp, Category.comp_id]
            rfl }
      isColimit := colimitOfDiagramTerminal isTerminalTop F
      fac := Category.id_comp _
      map_mem := by
        intro i hi
        induction i using WithTop.recTopCoe with
        | top => exact (hi isMax_top).elim
        | coe k =>
          have hk : (k : WithTop J) < Order.succ (k : WithTop J) :=
            Order.lt_succ_of_not_isMax hi
          let h : (k : WithTop J) ⟶ Order.succ (k : WithTop J) := homOfLE (Order.le_succ _)
          change W (colimMap (G.map h))
          refine IsStableUnderCobaseChange.of_isPushout
            (isPushout_colimMap_of_isIso (G.map h) k fun j hj ↦ ?_) ?_
          · have hjk : (j : WithTop J) < Order.succ (k : WithTop J) ↔ (j : WithTop J) < k :=
              ⟨fun h' ↦ lt_of_le_of_ne (Order.le_of_lt_succ h') (by simpa using hj),
                fun h' ↦ h'.trans_le (Order.le_succ _)⟩
            have : φ j (Order.succ (k : WithTop J)) ≤ φ j k := by simp only [φ, hjk, le_refl]
            have : IsIso ((hφ j).functor.map h) :=
              (iso_of_both_ways ((hφ j).functor.map h) (homOfLE this)).isIso_hom
            exact Functor.map_isIso (ComposableArrows.mk₁ (f j)) ((hφ j).functor.map h)
          · have h₀ : φ k k = 0 := by simp [φ]
            have h₁ : φ k (Order.succ (k : WithTop J)) = 1 := by simp [φ, hk]
            have key : (ComposableArrows.mk₁ (f k)).map ((hφ k).functor.map h) =
                (ComposableArrows.mk₁ (f k)).map (eqToHom h₀) ≫
                  (ComposableArrows.mk₁ (f k)).map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) ≫
                    (ComposableArrows.mk₁ (f k)).map (eqToHom h₁.symm) := by
              rw [← Functor.map_comp, ← Functor.map_comp]
              congr 1
            change W ((ComposableArrows.mk₁ (f k)).map ((hφ k).functor.map h))
            rw [key]
            have h₀' := Functor.map_isIso (ComposableArrows.mk₁ (f k)) (eqToHom h₀)
            have h₁' := Functor.map_isIso (ComposableArrows.mk₁ (f k)) (eqToHom h₁.symm)
            exact W.comp_mem _ _ (@of_isIso _ _ W _ _ _ _ _ h₀')
              (W.comp_mem _ _ (hf k) (@of_isIso _ _ W _ _ _ _ _ h₁')) }
  let e₁ : G.obj ⊥ ≅ Discrete.functor X₁ := Discrete.natIso fun j ↦
    (ComposableArrows.mk₁ (f j.as)).mapIso (eqToIso (by simp [φ] : φ j.as ⊥ = 0))
  let e₂ : G.obj ⊤ ≅ Discrete.functor X₂ := Discrete.natIso fun j ↦
    (ComposableArrows.mk₁ (f j.as)).mapIso (eqToIso (by simp [φ] : φ j.as ⊤ = 1))
  refine (W.arrow_mk_iso_iff (Arrow.isoMk (colim.mapIso e₁) (colim.mapIso e₂) ?_)).1
    (transfiniteCompositionsOfShape_le W (WithTop J) _ c.mem)
  apply colimit.hom_ext
  rintro ⟨j⟩
  have h₀ : (hφ j).functor.obj ⊥ = 0 := show φ j ⊥ = 0 by simp [φ]
  have h₁ : (hφ j).functor.obj ⊤ = 1 := show φ j ⊤ = 1 by simp [φ]
  have key : (ComposableArrows.mk₁ (f j)).map (eqToHom h₀) ≫
      (ComposableArrows.mk₁ (f j)).map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) =
      (ComposableArrows.mk₁ (f j)).map ((hφ j).functor.map (homOfLE bot_le : ⊥ ⟶ ⊤)) ≫
        (ComposableArrows.mk₁ (f j)).map (eqToHom h₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  change colimit.ι (G.obj ⊥) ⟨j⟩ ≫ colimMap e₁.hom ≫ Limits.Sigma.map f =
    colimit.ι (G.obj ⊥) ⟨j⟩ ≫ colimMap (G.map (homOfLE bot_le : ⊥ ⟶ ⊤)) ≫ colimMap e₂.hom
  rw [ι_colimMap_assoc, ι_colimMap_assoc, ι_colimMap,
    show colimit.ι (Discrete.functor X₁) ⟨j⟩ ≫ Limits.Sigma.map f = f j ≫ Sigma.ι X₂ j from
      Sigma.ι_map f j, ← Category.assoc, ← Category.assoc]
  exact key =≫ _

theorem IsCellularlyClosed.isStableUnderCoproducts [HasCoproducts.{w} C] (W : MorphismProperty C)
    [IsCellularlyClosed.{w} W] : W.IsStableUnderCoproducts.{w} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    rcases isEmpty_or_nonempty J with hJ | hJ
    · have : IsIso (Limits.Sigma.map f) := ⟨Sigma.desc fun j ↦ isEmptyElim j,
        Sigma.hom_ext _ _ fun j ↦ isEmptyElim j, Sigma.hom_ext _ _ fun j ↦ isEmptyElim j⟩
      exact isomorphisms_le_of_containsIdentities W _ (isomorphisms.infer_property _)
    · obtain ⟨_, _⟩ := exists_wellFoundedLT J
      exact sigmaMap_mem_of_wellFoundedLT W f hf

end Coproducts

theorem rlp_saturation (T : MorphismProperty C) : (saturation.{w} T).rlp = T.rlp := by
  refine le_antisymm (antitone_rlp (le_saturation T)) ?_
  rw [← rlp_llp_rlp T]
  exact antitone_rlp (saturation_le _ _ (le_llp_rlp T))

theorem saturation_eq_llp_rlp (T : MorphismProperty C) [T.HasSmallObjectArgument.{w}] :
    saturation.{w} T = T.rlp.llp := by
  refine le_antisymm (saturation_le _ _ (le_llp_rlp T)) ?_
  have := IsCardinalForSmallObjectArgument.hasCoproducts T (smallObjectκ.{w} T)
  have := IsCellularlyClosed.isStableUnderCoproducts.{w} (saturation.{w} T)
  rw [llp_rlp_of_hasSmallObjectArgument.{w} T, retracts_le_iff, transfiniteCompositions_le_iff,
    pushouts_le_iff, coproducts_le_iff]
  exact le_saturation T

theorem hasFunctorialFactorization_saturation (T : MorphismProperty C)
    [T.HasSmallObjectArgument.{w}] : HasFunctorialFactorization (saturation.{w} T) T.rlp := by
  rw [saturation_eq_llp_rlp T]
  infer_instance

theorem isWeakFactorizationSystem_saturation (T : MorphismProperty C)
    [T.HasSmallObjectArgument.{w}] :
    IsWeakFactorizationSystem (saturation.{w} T) (saturation.{w} T).rlp := by
  have := hasFunctorialFactorization_saturation T
  rw [rlp_saturation]
  exact ⟨rlp_saturation T, (saturation_eq_llp_rlp T).symm, inferInstance⟩

theorem exists_isCardinalPresentable_of_isSmall [IsLocallyPresentable.{v} C]
    (T : MorphismProperty C) [T.IsSmall.{v}] :
    ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular),
      ∀ ⦃X Y : C⦄ (i : X ⟶ Y), T i → IsCardinalPresentable X κ := by
  obtain ⟨ι, U, V, f, hf⟩ := (isSmall_iff_eq_ofHoms.{v} T).1 inferInstance
  have h : ∀ t, ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular), IsCardinalPresentable (U t) κ :=
    fun t ↦ Functor.IsAccessible.exists_cardinal (F := coyoneda.obj (Opposite.op (U t)))
  choose κ hκ hU using h
  obtain ⟨κ', hκ', hb⟩ := HasCardinalLT.exists_regular_cardinal_forall.{v}
    (fun t ↦ (κ t).ord.ToType)
  let : Fact κ'.IsRegular := ⟨hκ'⟩
  refine ⟨κ', inferInstance, fun X Y i hi ↦ ?_⟩
  rw [hf] at hi
  obtain ⟨t⟩ := hi
  let := hκ t
  let := hU t
  have ht : κ t < κ' := by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hb t
  exact isCardinalPresentable_of_le (U t) ht.le

instance hasSmallObjectArgument_of_isLocallyPresentable [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] (T : MorphismProperty C) [T.IsSmall.{v}] :
    T.HasSmallObjectArgument.{v} := by
  obtain ⟨κ', hκ', hAp⟩ := exists_isCardinalPresentable_of_isSmall T
  obtain ⟨ι, A, B, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{v} T).1 inferInstance
  have : Nonempty κ'.ord.ToType := by simpa using hκ'.out.ne_zero
  let : OrderBot κ'.ord.ToType := WellFoundedLT.toOrderBot _
  have hc : IsCardinalForSmallObjectArgument (ofHoms f) κ' :=
    { preservesColimit := by
        intro U V X Y i hi g hg
        let := hAp _ hi
        obtain ⟨t⟩ := hi
        have := preservesColimitsOfShape_of_isCardinalPresentable (A t) κ' κ'.ord.ToType
        infer_instance }
  exact ⟨κ', hκ', inferInstance, hc⟩

end MorphismProperty

end CategoryTheory
