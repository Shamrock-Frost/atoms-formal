import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Atoms.Homotopical.Cellular.Model
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

def attachPreserving (P : (Aᵒᵖ ⥤ Type (max w v)) → Prop) :
    MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  fun X Y f ↦ Mono f ∧ ∀ ⦃Z W : Aᵒᵖ ⥤ Type (max w v)⦄ (g : X ⟶ Z) (f' : Z ⟶ W) (g' : Y ⟶ W),
    IsPushout f g g' f' → P Z → P W

structure IsMonoSaturatedClass (P : (Aᵒᵖ ⥤ Type (max w v)) → Prop) : Prop where
  of_isPushout : ∀ {X₀ X₁ X₂ X₃ : Aᵒᵖ ⥤ Type (max w v)} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂}
    {g₁ : X₁ ⟶ X₃} {g₂ : X₂ ⟶ X₃}, IsPushout f₁ f₂ g₁ g₂ → Mono f₁ →
      P X₀ → P X₁ → P X₂ → P X₃
  of_isColimit : ∀ (J : Type (max w v)) [LinearOrder J] [WellFoundedLT J]
    (F : J ⥤ Aᵒᵖ ⥤ Type (max w v)),
    (∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) →
      ∀ {c : Cocone F}, IsColimit c → (∀ j, P (F.obj j)) → P c.pt

namespace IsMonoSaturatedClass

variable {P : (Aᵒᵖ ⥤ Type (max w v)) → Prop}

theorem of_iso (hP : IsMonoSaturatedClass P) {X Y : Aᵒᵖ ⥤ Type (max w v)} (e : X ≅ Y) (hX : P X) :
    P Y := by
  let c : Cocone ((Functor.const (ULift.{max w v} (Fin 1))).obj X) :=
    { pt := Y
      ι := { app := fun _ ↦ e.hom } }
  have hc : IsColimit c :=
    { desc := fun s ↦ e.inv ≫ s.ι.app ⟨0⟩
      fac := fun s j ↦ by rw [Subsingleton.elim j ⟨0⟩]; simp [c]
      uniq := fun s m hm ↦ by rw [← hm ⟨0⟩]; simp [c] }
  exact hP.of_isColimit _ _ (fun _ _ _ ↦ by dsimp; infer_instance) hc (fun _ ↦ hX)

theorem initial (hP : IsMonoSaturatedClass P) : P (⊥_ (Aᵒᵖ ⥤ Type (max w v))) := by
  let F : ULift.{max w v} (Fin 0) ⥤ Aᵒᵖ ⥤ Type (max w v) :=
    { obj := fun j ↦ j.down.elim0
      map := fun {j} _ ↦ j.down.elim0
      map_id := fun j ↦ j.down.elim0
      map_comp := fun {j} _ _ _ ↦ j.down.elim0 }
  let c : Cocone F :=
    { pt := ⊥_ _
      ι := { app := fun j ↦ j.down.elim0, naturality := fun j ↦ j.down.elim0 } }
  have hc : IsColimit c :=
    { desc := fun s ↦ initial.to s.pt
      fac := fun _ j ↦ j.down.elim0
      uniq := fun _ _ _ ↦ initial.hom_ext _ _ }
  exact hP.of_isColimit _ F (fun i ↦ i.down.elim0) hc (fun j ↦ j.down.elim0)

private def isInitialBotToFunctor {X : Aᵒᵖ ⥤ Type (max w v)} :
    IsInitial (⊥ : Subfunctor X).toFunctor :=
  IsInitial.ofUniqueHom
    (fun Y ↦
      { app a := ↾fun x ↦ absurd x.2 (by simp)
        naturality a b f := by
          ext x
          exact absurd x.2 (by simp) })
    fun Y f ↦ by
      ext a x
      exact absurd x.2 (by simp)

theorem iSup_subfunctor
    (hP : IsMonoSaturatedClass P) {X : Aᵒᵖ ⥤ Type (max w v)} (J : Type (max w v)) [LinearOrder J]
    [WellFoundedLT J] (G : J → Subfunctor X) (hG : Monotone G) (h : ∀ j, P (G j).toFunctor) :
    P (⨆ j, G j).toFunctor :=
  hP.of_isColimit J (hG.functor ⋙ Subfunctor.toFunctorFunctor X)
    (fun _ _ h ↦ inferInstanceAs (Mono (Subfunctor.homOfLe (hG h))))
    (isColimitOfPreserves (Subfunctor.toFunctorFunctor X)
      (Preorder.colimitCoconeOfIsLUB hG.functor isLUB_iSup).isColimit) h

theorem bot_subfunctor
    (hP : IsMonoSaturatedClass P) (X : Aᵒᵖ ⥤ Type (max w v)) : P (⊥ : Subfunctor X).toFunctor :=
  hP.of_iso ((isInitialBotToFunctor (X := X)).uniqueUpToIso initialIsInitial).symm hP.initial

end IsMonoSaturatedClass

section Colimit

variable {K : Type (max w v)} [Category.{max w v} K] [IsConnected K]
  {G G' : K ⥤ Aᵒᵖ ⥤ Type (max w v)}
  {X₀ Z : Aᵒᵖ ⥤ Type (max w v)} (a : ∀ k, X₀ ⟶ G.obj k) (b : ∀ k, Z ⟶ G'.obj k)
  (ι : ∀ k, G.obj k ⟶ G'.obj k) (g₀ : X₀ ⟶ Z)

noncomputable def isColimitOfIsPushout
    (hι : ∀ {k k'} (φ : k ⟶ k'), G.map φ ≫ ι k' = ι k ≫ G'.map φ)
    (hb : ∀ {k k'} (φ : k ⟶ k'), b k ≫ G'.map φ = b k')
    (h : ∀ k, IsPushout (a k) g₀ (ι k) (b k)) {c : Cocone G} (hc : IsColimit c)
    (c' : Cocone G') (e : X₀ ⟶ c.pt) (he : ∀ k, a k ≫ c.ι.app k = e) (u : c.pt ⟶ c'.pt)
    (hu : ∀ k, c.ι.app k ≫ u = ι k ≫ c'.ι.app k) (w : Z ⟶ c'.pt)
    (hw : ∀ k, b k ≫ c'.ι.app k = w) (hW : IsPushout e g₀ u w) : IsColimit c' := by
  let k₀ : K := Classical.arbitrary K
  have hs : ∀ (s : Cocone G') k, b k ≫ s.ι.app k = b k₀ ≫ s.ι.app k₀ := fun s k ↦
    constant_of_preserves_morphisms (fun k ↦ b k ≫ s.ι.app k)
      (fun k k' φ ↦ by rw [← s.w φ, ← Category.assoc, hb]) k k₀
  let t (s : Cocone G') : Cocone G :=
    { pt := s.pt
      ι := { app := fun k ↦ ι k ≫ s.ι.app k
             naturality := fun k k' φ ↦ by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               rw [← Category.assoc, hι, Category.assoc, s.w] } }
  have hd : ∀ s : Cocone G', e ≫ hc.desc (t s) = g₀ ≫ b k₀ ≫ s.ι.app k₀ := fun s ↦ by
    rw [← he k₀, Category.assoc, hc.fac (t s) k₀, ← Category.assoc, (h k₀).w,
      Category.assoc]
  refine
    { desc := fun s ↦ hW.desc (hc.desc (t s)) (b k₀ ≫ s.ι.app k₀) (hd s)
      fac := fun s k ↦ ?_
      uniq := fun s m hm ↦ ?_ }
  · refine (h k).hom_ext ?_ ?_
    · rw [← Category.assoc, ← hu, Category.assoc, hW.inl_desc, hc.fac (t s) k]
    · rw [← Category.assoc, hw, hW.inr_desc, hs s k]
  · refine hW.hom_ext ?_ ?_
    · rw [hW.inl_desc]
      refine hc.hom_ext fun k ↦ ?_
      rw [← Category.assoc, hu, Category.assoc, hm, hc.fac (t s) k]
    · rw [hW.inr_desc, ← hw k₀, Category.assoc, hm]

end Colimit

section Chain

variable {J : Type (max w v)} [LinearOrder J] [OrderBot J] {Z : Aᵒᵖ ⥤ Type (max w v)}

noncomputable def pushoutChain (F : J ⥤ Aᵒᵖ ⥤ Type (max w v)) (g₀ : F.obj ⊥ ⟶ Z) :
    J ⥤ Aᵒᵖ ⥤ Type (max w v) :=
  F.toUnder (F.obj ⊥) (fun _ ↦ F.map (homOfLE bot_le))
    (fun _ ↦ by rw [← Functor.map_comp]; rfl) ⋙ Under.pushout g₀ ⋙ Under.forget Z

variable (F : J ⥤ Aᵒᵖ ⥤ Type (max w v)) (g₀ : F.obj ⊥ ⟶ Z)

noncomputable def pushoutChainInl (j : J) : F.obj j ⟶ (pushoutChain F g₀).obj j :=
  pushout.inl (F.map (homOfLE bot_le : ⊥ ⟶ j)) g₀

noncomputable def pushoutChainInr (j : J) : Z ⟶ (pushoutChain F g₀).obj j :=
  pushout.inr (F.map (homOfLE bot_le : ⊥ ⟶ j)) g₀

theorem isPushout_pushoutChain (j : J) :
    IsPushout (F.map (homOfLE bot_le : ⊥ ⟶ j)) g₀ (pushoutChainInl F g₀ j)
      (pushoutChainInr F g₀ j) :=
  IsPushout.of_hasPushout _ _

theorem pushoutChainInl_map {i j : J} (φ : i ⟶ j) :
    pushoutChainInl F g₀ i ≫ (pushoutChain F g₀).map φ =
      F.map φ ≫ pushoutChainInl F g₀ j :=
  pushout.inl_desc _ _ _

theorem pushoutChainInr_map {i j : J} (φ : i ⟶ j) :
    pushoutChainInr F g₀ i ≫ (pushoutChain F g₀).map φ = pushoutChainInr F g₀ j :=
  pushout.inr_desc _ _ _

theorem isPushout_pushoutChain_map {i j : J} (φ : i ⟶ j) :
    IsPushout (F.map φ) (pushoutChainInl F g₀ i) (pushoutChainInl F g₀ j)
      ((pushoutChain F g₀).map φ) := by
  refine IsPushout.of_left ?_ (pushoutChainInl_map F g₀ φ).symm
    (isPushout_pushoutChain F g₀ i)
  rw [← Functor.map_comp, pushoutChainInr_map]
  exact isPushout_pushoutChain F g₀ j

theorem mono_pushoutChain_map (hF : ∀ {i j : J} (φ : i ⟶ j), Mono (F.map φ)) {i j : J}
    (φ : i ⟶ j) : Mono ((pushoutChain F g₀).map φ) :=
  (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).of_isPushout
    (isPushout_pushoutChain_map F g₀ φ).flip (hF φ)

attribute [local instance] IsFiltered.isConnected

noncomputable def isColimitPushoutChain [F.IsWellOrderContinuous] (j : J)
    (hj : Order.IsSuccLimit j) :
    IsColimit ((Set.principalSegIio j).cocone (pushoutChain F g₀)) :=
  haveI : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  isColimitOfIsPushout (G := (Set.principalSegIio j).monotone.functor ⋙ F)
    (G' := (Set.principalSegIio j).monotone.functor ⋙ pushoutChain F g₀)
    (fun k ↦ F.map (homOfLE bot_le : ⊥ ⟶ k.1)) (fun k ↦ pushoutChainInr F g₀ k.1)
    (fun k ↦ pushoutChainInl F g₀ k.1) g₀ (fun _ ↦ pushoutChainInl_map F g₀ _ |>.symm)
    (fun _ ↦ pushoutChainInr_map F g₀ _) (fun k ↦ isPushout_pushoutChain F g₀ k.1)
    (F.isColimitOfIsWellOrderContinuous j hj) _ (F.map (homOfLE bot_le : ⊥ ⟶ j))
    (fun _ ↦ (F.map_comp _ _).symm) (pushoutChainInl F g₀ j)
    (fun _ ↦ (pushoutChainInl_map F g₀ _).symm) (pushoutChainInr F g₀ j)
    (fun _ ↦ pushoutChainInr_map F g₀ _) (isPushout_pushoutChain F g₀ j)

end Chain

section Saturation

variable {P : (Aᵒᵖ ⥤ Type (max w v)) → Prop} (hP : IsMonoSaturatedClass P)
  {J : Type (max w v)} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : Aᵒᵖ ⥤ Type (max w v)} {f : X ⟶ Y}

theorem mono_map_of_transfiniteCompositionOfShape
    (hf : (attachPreserving P).TransfiniteCompositionOfShape J f) {i j : J} (φ : i ⟶ j) :
    Mono (hf.F.map φ) :=
  (hf.ofLE (W' := MorphismProperty.monomorphisms _) fun _ _ _ h ↦ h.1).mem_map φ

include hP in
theorem prop_pushoutChain_obj (hf : (attachPreserving P).TransfiniteCompositionOfShape J f)
    {Z : Aᵒᵖ ⥤ Type (max w v)} (g₀ : hf.F.obj ⊥ ⟶ Z) (hZ : P Z) (j : J) :
    P ((pushoutChain hf.F g₀).obj j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    have : IsIso (hf.F.map (homOfLE bot_le : (⊥ : J) ⟶ ⊥)) := by
      rw [show (homOfLE bot_le : (⊥ : J) ⟶ ⊥) = 𝟙 _ from rfl]
      infer_instance
    have := (isPushout_pushoutChain hf.F g₀ ⊥).isIso_inr_of_isIso
    exact hP.of_iso (asIso (pushoutChainInr hf.F g₀ ⊥)) hZ
  | succ j hj hj' =>
    exact (hf.map_mem j hj).2 _ _ _ (isPushout_pushoutChain_map hf.F g₀ _) hj'
  | isSuccLimit j hj hj' =>
    exact hP.of_isColimit (Set.Iio j) _
      (fun _ _ _ ↦ mono_pushoutChain_map hf.F g₀
        (mono_map_of_transfiniteCompositionOfShape hf) _)
      (isColimitPushoutChain hf.F g₀ j hj) (fun k ↦ hj' k.1 k.2)

end Saturation

theorem isStableUnderTransfiniteComposition_attachPreserving {P : (Aᵒᵖ ⥤ Type (max w v)) → Prop}
    (hP : IsMonoSaturatedClass P) :
    (attachPreserving P).IsStableUnderTransfiniteComposition.{max w v} := by
  refine ⟨fun J _ _ _ _ ↦ ⟨fun X Y f ⟨hf⟩ ↦ ⟨?_, fun Z W g f' g' sq hZ ↦ ?_⟩⟩⟩
  · exact (MorphismProperty.monomorphisms _).transfiniteCompositionsOfShape_le J f
      (hf.ofLE fun _ _ _ h ↦ h.1).mem
  let g₀ := hf.isoBot.hom ≫ g
  have hd : ∀ j, hf.F.map (homOfLE bot_le : ⊥ ⟶ j) ≫ hf.incl.app j ≫ g' = g₀ ≫ f' := fun j ↦ by
    rw [← Category.assoc, hf.toTransfiniteCompositionOfShape.map_bot_comp_incl_app,
      Category.assoc, sq.w, Category.assoc]
  let c' : Cocone (pushoutChain hf.F g₀) :=
    { pt := W
      ι :=
        { app := fun j ↦ (isPushout_pushoutChain hf.F g₀ j).desc (hf.incl.app j ≫ g') f' (hd j)
          naturality := fun i j φ ↦ by
            refine (isPushout_pushoutChain hf.F g₀ i).hom_ext ?_ ?_
            · rw [reassoc_of% (pushoutChainInl_map hf.F g₀ φ), IsPushout.inl_desc,
                ← Category.assoc, hf.incl.naturality]
              simp
            · rw [← Category.assoc, pushoutChainInr_map hf.F g₀ φ, IsPushout.inr_desc]
              simp } }
  exact hP.of_isColimit J _
    (fun _ _ _ ↦ mono_pushoutChain_map hf.F g₀ (mono_map_of_transfiniteCompositionOfShape hf) _)
    (c := c')
    (isColimitOfIsPushout (fun k ↦ hf.F.map (homOfLE bot_le : ⊥ ⟶ k))
      (pushoutChainInr hf.F g₀) (pushoutChainInl hf.F g₀) g₀
      (fun _ ↦ (pushoutChainInl_map hf.F g₀ _).symm) (fun _ ↦ pushoutChainInr_map hf.F g₀ _)
      (isPushout_pushoutChain hf.F g₀) hf.isColimit c' (hf.isoBot.hom ≫ f)
      hf.toTransfiniteCompositionOfShape.map_bot_comp_incl_app g'
      (fun k ↦ ((isPushout_pushoutChain hf.F g₀ k).inl_desc _ _ _).symm) f'
      (fun k ↦ (isPushout_pushoutChain hf.F g₀ k).inr_desc _ _ _)
      (sq.of_iso' hf.isoBot (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _).symm
        (by simp [g₀])
        (by simp) (by simp)))
    (prop_pushoutChain_obj hP hf g₀ hZ)

theorem isSaturated_attachPreserving {P : (Aᵒᵖ ⥤ Type (max w v)) → Prop}
    (hP : IsMonoSaturatedClass P)
    (hretract : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X) :
    IsSaturated.{max w v} (attachPreserving P) where
  isStableUnderCobaseChange :=
    ⟨fun sq hf ↦ ⟨(MorphismProperty.monomorphisms _).of_isPushout sq hf.1,
      fun _ _ _ _ _ sq' hZ ↦ hf.2 _ _ _ (sq.flip.paste_vert sq') hZ⟩⟩
  isStableUnderRetracts := by
    refine ⟨fun {X Y X' Y' f g} r hg ↦
      ⟨(MorphismProperty.monomorphisms _).of_retract r hg.1, fun Z W φ f'' ψ sq hZ ↦ ?_⟩⟩
    have sq₁ := IsPushout.of_hasPushout g (r.r.left ≫ φ)
    have h₁ : f ≫ r.i.right ≫ pushout.inl g (r.r.left ≫ φ) = φ ≫ pushout.inr _ _ := by
      rw [← r.i_w_assoc, sq₁.w]
      simp
    have h₂ : g ≫ r.r.right ≫ ψ = (r.r.left ≫ φ) ≫ f'' := by
      rw [← r.r_w_assoc, sq.w, Category.assoc]
    refine hretract (sq.desc (r.i.right ≫ pushout.inl _ _) (pushout.inr _ _) h₁)
      (sq₁.desc (r.r.right ≫ ψ) f'' h₂) ?_ (hg.2 _ _ _ sq₁ hZ)
    refine sq.hom_ext ?_ ?_
    · rw [sq.inl_desc_assoc, Category.assoc, sq₁.inl_desc, r.retract_right_assoc,
        Category.comp_id]
      exact Category.id_comp ψ
    · rw [sq.inr_desc_assoc, sq₁.inr_desc, Category.comp_id]
  isStableUnderTransfiniteComposition :=
    isStableUnderTransfiniteComposition_attachPreserving hP

theorem forall_of_saturation_eq {P : (Aᵒᵖ ⥤ Type (max w v)) → Prop} (hP : IsMonoSaturatedClass P)
    (hretract : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X)
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hS : saturation.{max w v} S = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (hgen : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), S f → P X ∧ P Y)
    (X : Aᵒᵖ ⥤ Type (max w v)) :
    P X := by
  have hle : S ≤ attachPreserving P := fun _ _ f hf ↦
    ⟨by simpa only [hS] using le_saturation.{max w v} S f hf,
      fun _ _ _ _ _ sq hZ ↦ hP.of_isPushout sq
        (by simpa only [hS] using le_saturation.{max w v} S f hf)
        (hgen f hf).1 (hgen f hf).2 hZ⟩
  have := isSaturated_attachPreserving hP hretract
  have hX := saturation_le.{max w v} S (attachPreserving P) hle (initial.to X)
    (by rw [hS]; exact monomorphisms.infer_property _)
  exact hX.2 _ _ _ (IsPushout.id_vert (initial.to X)) hP.initial

end Atoms.Homotopical
