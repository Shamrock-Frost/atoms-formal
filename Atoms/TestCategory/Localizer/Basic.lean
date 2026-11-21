import Atoms.TestCategory.SeparatingIntervalCriterion
import Atoms.TestCategory.Presheaf.PrelocalizerPushout
import Atoms.TestCategory.Presheaf.PrelocalizerChain

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

theorem wPsh_isStableUnderCobaseChange :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u) ⊓ 𝒲.wPsh A).IsStableUnderCobaseChange where
  of_isPushout {X₀ X₁ X₂ X'} {f g f' g'} sq hf := by
    have : Mono f := hf.1
    refine ⟨(MorphismProperty.monomorphisms _).of_isPushout sq hf.1, ?_⟩
    exact 𝒲.wPsh_of_isPushout A (IsPushout.id_horiz g) sq.flip (𝟙 X₀) f (𝟙 X₂) f'
      (by simp) (by simp) sq.w (by simp) ((𝒲.wPsh A).id_mem X₀) hf.2
      ((𝒲.wPsh A).id_mem X₂)

theorem wPsh_cocone_ι_app_bot {K : Type u} [LinearOrder K] [WellFoundedLT K] [OrderBot K]
    (G : K ⥤ Aᵒᵖ ⥤ Type u) (hmono : ∀ (i j : K) (h : i ≤ j), Mono (G.map (homOfLE h)))
    (hG : ∀ k : K, 𝒲.wPsh A (G.map (homOfLE (bot_le : ⊥ ≤ k)))) {c : Cocone G}
    (hc : IsColimit c) : 𝒲.wPsh A (c.ι.app ⊥) := by
  let φ : (Functor.const K).obj (G.obj ⊥) ⟶ G :=
    { app k := G.map (homOfLE bot_le)
      naturality i j f := by
        dsimp
        rw [Category.id_comp, ← G.map_comp]
        rfl }
  have : IsConnected K := isConnected_of_isInitial K isInitialBot
  refine 𝒲.wPsh_of_isColimit A (fun i j h => ?_) hmono φ hG
    (isColimitConstCocone K (G.obj ⊥)) hc (c.ι.app ⊥) (fun k => ?_)
  · dsimp
    infer_instance
  · dsimp [φ]
    simp only [constCocone_ι, NatTrans.id_app]
    exact (Category.id_comp _).trans (c.w _).symm

theorem wPsh_isStableUnderTransfiniteComposition :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u) ⊓
      𝒲.wPsh A).IsStableUnderTransfiniteComposition.{u} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := ⟨fun X Y f ⟨hf⟩ => by
    have hmono : ∀ {i j : J} (φ : i ⟶ j), Mono (hf.F.map φ) := fun φ =>
      (hf.ofLE inf_le_left).mem_map φ
    have hbot : ∀ j : J, 𝒲.wPsh A (hf.F.map (homOfLE (bot_le : ⊥ ≤ j))) := by
      intro j
      induction j using SuccOrder.limitRecOn with
      | isMin j hj =>
        obtain rfl := hj.eq_bot
        simpa using (𝒲.wPsh A).id_mem _
      | succ j hj hj' =>
        rw [← homOfLE_comp bot_le (Order.le_succ j), hf.F.map_comp]
        exact (𝒲.wPsh A).comp_mem _ _ hj' (hf.map_mem j hj).2
      | isSuccLimit j hj hj' =>
        let : OrderBot (Set.Iio j) :=
          { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
            bot_le k := bot_le }
        exact 𝒲.wPsh_cocone_ι_app_bot A (K := Set.Iio j)
          ((Set.principalSegIio j).monotone.functor ⋙ hf.F) (fun _ _ _ => hmono _)
          (fun k => hj' k.1 k.2) (hf.F.isColimitOfIsWellOrderContinuous j hj)
    have hincl : 𝒲.wPsh A (hf.incl.app ⊥) :=
      𝒲.wPsh_cocone_ι_app_bot A hf.F (fun _ _ _ => hmono _) hbot hf.isColimit
    refine ⟨(MorphismProperty.monomorphisms _).transfiniteCompositionsOfShape_le J f
      ⟨hf.ofLE inf_le_left⟩, ?_⟩
    rw [← hf.fac]
    exact (𝒲.wPsh A).comp_mem _ _
      (isomorphisms_le_of_containsIdentities 𝒲.W _ (isomorphisms.infer_property _)) hincl⟩

theorem locallyAspherical_nerveFunctor_obj_of_isLocalTest [hA : 𝒲.IsLocalTest A]
    (C : Cat.{u, u}) [HasTerminal C] : 𝒲.LocallyAspherical A ((nerveFunctor A).obj C) := by
  intro a
  rw [← pshAspherical_nerveFunctor_over_iff]
  have e : terminal.from ((elementsFunctor (Over a)).obj ((nerveFunctor (Over a)).obj C)) =
      (nerveAdjunction (Over a)).counit.app C ≫ terminal.from C := terminal.hom_ext _ _
  change 𝒲.W (terminal.from _)
  rw [e]
  exact 𝒲.W.comp_mem _ _ ((hA.isWeakTest_over a).counit_mem C) (𝒲.terminal_aspherical C)

end BasicLocalizer

variable {A} in
def nervePoint (b : Bool) :
    (⊤_ (Aᵒᵖ ⥤ Type u)) ⟶ (nerveFunctor A).obj interval.{u} where
  app _ := TypeCat.ofHom fun _ =>
    ((Functor.const _).obj (ULift.up b : interval.{u})).toCatHom
  naturality _ _ _ := by
    ext
    rfl

variable {A} in
theorem isPullback_nervePoint :
    IsPullback (initial.to (⊤_ (Aᵒᵖ ⥤ Type u))) (initial.to (⊤_ (Aᵒᵖ ⥤ Type u)))
      (nervePoint false) (nervePoint true) := by
  have hempty : ∀ (s : PullbackCone (nervePoint false) (nervePoint true)) (x : Aᵒᵖ)
      (y : s.pt.obj x), False := by
    intro s x y
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.condition x) y
    have h' := congr_arg (fun F : Cat.of (Over x.unop) ⟶ interval.{u} =>
      (F.toFunctor.obj (Over.mk (𝟙 x.unop))).down) h
    exact Bool.false_ne_true h'
  have hinit : ∀ s : PullbackCone (nervePoint false) (nervePoint true), IsInitial s.pt :=
    fun s => IsInitial.ofUniqueHom
      (fun Z => { app x := TypeCat.ofHom fun y => (hempty s x y).elim
                  naturality x _ _ := by
                    ext y
                    exact (hempty s x y).elim })
      (fun Z m => by
        ext x y
        exact (hempty s x y).elim)
  have w : initial.to (⊤_ (Aᵒᵖ ⥤ Type u)) ≫ nervePoint false =
      initial.to (⊤_ (Aᵒᵖ ⥤ Type u)) ≫ nervePoint true := initial.hom_ext _ _
  exact ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w (fun s => (hinit s).to _)
    (fun s => (hinit s).hom_ext _ _) (fun s => (hinit s).hom_ext _ _)
    (fun s _ _ _ => (hinit s).hom_ext _ _)⟩⟩

namespace BasicLocalizer

theorem rlp_monomorphisms_le_wPsh_of_isLocalTest [𝒲.IsLocalTest A] :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A :=
  𝒲.rlp_monomorphisms_le_wPsh_of_separatingInterval A
    ⟨(nerveFunctor A).obj interval, nervePoint, isPullback_nervePoint⟩
    (𝒲.locallyAspherical_nerveFunctor_obj_of_isLocalTest A _)

instance isALocalizer_wPsh_of_isLocalTest [𝒲.IsLocalTest A] :
    Homotopical.IsALocalizer (𝒲.wPsh A) where
  hasTwoOutOfThreeProperty := inferInstance
  rlp_monomorphisms_le := 𝒲.rlp_monomorphisms_le_wPsh_of_isLocalTest A
  isStableUnderCobaseChange := 𝒲.wPsh_isStableUnderCobaseChange A
  isStableUnderTransfiniteComposition := 𝒲.wPsh_isStableUnderTransfiniteComposition A

theorem isALocalizer_wPsh_iff : Homotopical.IsALocalizer (𝒲.wPsh A) ↔ 𝒲.IsLocalTest A :=
  ⟨fun h => 𝒲.isLocalTest_of_rlp_le A h.rlp_monomorphisms_le,
    fun _ => inferInstance⟩

end BasicLocalizer

end Atoms.TestCategory
