import Atoms.Diagrammatic.ClosedSubpresheafPushout
import Atoms.Diagrammatic.Horn.Basic

open Order CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem homOfLe_mem_saturation_of_eq (U : Atom) {A B : LowerSet U.ogp} (h : A ≤ B)
    (e : A = B) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) := by
  subst e
  have hid : Subfunctor.homOfLe (closedSubpresheaf_mono U h) = 𝟙 _ := by
    ext
    rfl
  rw [hid]
  exact MorphismProperty.id_mem _ _

theorem homOfLe_mem_saturation_of_eq_left (U : Atom) {A A' B : LowerSet U.ogp}
    (h : A ≤ B) (h' : A' ≤ B) (e : A = A')
    (hm : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h'))) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) := by
  subst e
  exact hm

theorem homOfLe_mem_saturation_trans (U : Atom) {A B C : LowerSet U.ogp} (h₁ : A ≤ B)
    (h₂ : B ≤ C) (h : A ≤ C)
    (hm₁ : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h₁)))
    (hm₂ : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h₂))) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) := by
  have hc := MorphismProperty.comp_mem _ _ _ hm₁ hm₂
  have e : Subfunctor.homOfLe (closedSubpresheaf_mono U h₁) ≫
        Subfunctor.homOfLe (closedSubpresheaf_mono U h₂) =
      Subfunctor.homOfLe (closedSubpresheaf_mono U h) := by
    ext
    rfl
  rwa [e] at hc

theorem homOfLe_mem_saturation_of_inter_eq (U : Atom) {A B C D : LowerSet U.ogp}
    (hC : A ⊓ B = C) (hD : A ⊔ B = D)
    (hCB : C ≤ B) (hAD : A ≤ D)
    (hm : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U hCB))) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U hAD)) := by
  subst hC hD
  exact MorphismProperty.of_isPushout (isPushout_closedSubpresheaf U A B) hm

theorem homOfLe_cond_mem_saturation_of_isPastingIn (U : Atom) {k : ℕ} (δ : Bool)
    {A B C : LowerSet U.ogp} (hp : U.ogp.IsPastingIn k (cond δ A B) (cond δ B A) C)
    (hY : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (boundary_le A k δ))))
    (h : B ≤ C) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) :=
  have hc := (isPastingIn_cond_iff δ).1 hp
  homOfLe_mem_saturation_of_inter_eq U ((inf_comm B A).trans hc.2.2) ((sup_comm B A).trans hc.1)
    (boundary_le A k δ) h hY

private theorem sup_boundary_aux {α : Type*} [DistribLattice α] {V W dV dW : α}
    (bVV : dV ≤ V) (bWW : dW ≤ W) (sV : V ⊓ W ≤ dV) (sW : V ⊓ W ≤ dW) :
    (dV ⊔ dW) ⊓ V = dV ∧ (dV ⊔ dW) ⊔ V = V ⊔ dW ∧ (V ⊔ dW) ⊓ W = dW ∧
      (V ⊔ dW) ⊔ W = V ⊔ W :=
  ⟨by rw [inf_sup_right, inf_eq_left.2 bVV,
       sup_eq_left.2 ((inf_le_inf_right V bWW).trans (inf_comm W V ▸ sV))],
   by rw [sup_right_comm, sup_eq_right.2 bVV],
   by rw [inf_sup_right, inf_eq_left.2 bWW, sup_eq_right.2 sW],
   by rw [sup_assoc, sup_eq_right.2 bWW]⟩

theorem homOfLe_boundary_mem_saturation_of_isPastingIn_of_lt (U : Atom) {i k : ℕ}
    {V W B : LowerSet U.ogp} (hp : U.ogp.IsPastingIn i V W B) (gV : U.ogp.IsGlobular V)
    (gW : U.ogp.IsGlobular W) (hik : i < k) (α : Bool)
    (hVk : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (boundary_le V k α))))
    (hWk : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U (boundary_le W k α))))
    (h : U.ogp.boundary B k α ≤ B) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) := by
  have hbeq := (hp.boundary_of_lt gV gW hik α).sup_eq.symm
  have bVV := boundary_le V k α
  have bWW := boundary_le W k α
  have sV : V ⊓ W ≤ U.ogp.boundary V k α := by
    rw [hp.inf_eq_output]; exact gV.boundary_le_boundary hik true α
  have sW : V ⊓ W ≤ U.ogp.boundary W k α := by
    rw [hp.inf_eq_input]; exact gW.boundary_le_boundary hik false α
  have h₁ : U.ogp.boundary B k α ≤ V ⊔ U.ogp.boundary W k α := by
    rw [hbeq]; exact sup_le_sup bVV le_rfl
  have h₂ : V ⊔ U.ogp.boundary W k α ≤ B := by
    rw [← hp.sup_eq]; exact sup_le_sup le_rfl bWW
  obtain ⟨e₁, e₂, e₃, e₄⟩ := sup_boundary_aux bVV bWW sV sW
  refine homOfLe_mem_saturation_trans U h₁ h₂ h ?_ ?_
  · refine homOfLe_mem_saturation_of_inter_eq U ?_ ?_ bVV h₁ hVk
    · rw [hbeq]; exact e₁
    · rw [hbeq]; exact e₂
  · refine homOfLe_mem_saturation_of_inter_eq U ?_ ?_ bWW h₂ hWk
    · exact e₃
    · rw [← hp.sup_eq]; exact e₄

theorem homOfLe_bdry_closure_iso (U : Atom) (x : U.ogp) (hx : 0 < grade ℕ x)
    (α : Bool) :
    Nonempty (Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono U
        (boundary_le (LowerSet.Iic x) (grade ℕ x - 1) α))) ≅
      Arrow.mk (hornInclusion.{u} (principalHornData U x hx α))) :=
  ⟨(homOfLeImageArrowIso (Atom.closureIncl U x) (Atom.isInclusionHom_closureIncl U x)
      le_top (boundary_le (LowerSet.Iic x) (grade ℕ x - 1) α)
      (SetLike.coe_injective (image_hornSubset_principalHornData U x hx α))
      (Atom.map_closureInclOGP_top U x)).symm ≪≫
    homOfLeUnivArrowIso (Atom.ofClosure U x) (hornSubset (principalHornData U x hx α))⟩

theorem homOfLe_boundary_closure_mem_saturation (U : Atom) (x : U.ogp)
    (hx : 0 < grade ℕ x) (α : Bool) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U
        (boundary_le (LowerSet.Iic x) (grade ℕ x - 1) α))) := by
  obtain ⟨e⟩ := homOfLe_bdry_closure_iso U x hx α
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2
    (MorphismProperty.le_saturation _ _ (MorphismProperty.ofHoms.mk _))

theorem homOfLe_boundary_mem_saturation (U : Atom) {B : LowerSet U.ogp}
    (hB : IsMoleculeIn U.ogp B) (k : ℕ) (α : Bool) :
    MorphismProperty.saturation.{u} hornInclusions.{u} (Subfunctor.homOfLe (closedSubpresheaf_mono U
      (boundary_le B k α))) := by
  induction hB generalizing k α with
  | point x hx =>
    refine homOfLe_mem_saturation_of_eq U (boundary_le _ k α) (boundary_eq_self ?_ α)
    rw [LowerSet.krullDim_Iic_of_isMin hx]
    exact_mod_cast Nat.zero_le k
  | atom t hr _ ih =>
    rcases le_or_gt (krullDim (LowerSet.Iic t)) k with hk | hk
    · exact homOfLe_mem_saturation_of_eq U (boundary_le _ k α) (boundary_eq_self hk α)
    rw [LowerSet.krullDim_Iic, Nat.cast_lt] at hk
    have ht : 0 < grade ℕ t := by omega
    rcases (Nat.le_sub_one_of_lt hk).eq_or_lt with hkt | hkt
    · subst hkt
      exact homOfLe_boundary_closure_mem_saturation U t ht α
    · have hdim : krullDim (LowerSet.Iic t) = (grade ℕ t - 1 : ℕ) + 1 := by
        rw [LowerSet.krullDim_Iic, ← Nat.cast_add_one, Nat.sub_add_cancel ht]
      have hcl : U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) α =
          U.ogp.bdry (LowerSet.Iic t) α := (bdry_eq_boundary hdim α).symm
      have hm₁ : MorphismProperty.saturation.{u} hornInclusions.{u}
          (Subfunctor.homOfLe (closedSubpresheaf_mono U
            (boundary_le (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) α) k α))) := by
        rw [hcl]
        exact ih α k α
      have hm₂ := homOfLe_boundary_closure_mem_saturation U t ht α
      have s₁ := boundary_le (U.ogp.boundary (LowerSet.Iic t) (grade ℕ t - 1) α) k α
      have s₂ := boundary_le (LowerSet.Iic t) (grade ℕ t - 1) α
      exact homOfLe_mem_saturation_of_eq_left U (boundary_le (LowerSet.Iic t) k α) (s₁.trans s₂)
        (hr.isGlobular k (grade ℕ t - 1) hkt α α).symm
        (homOfLe_mem_saturation_trans U s₁ s₂ (s₁.trans s₂) hm₁ hm₂)
  | paste i V W B hp hV hW _ ihV ihW =>
    have gV := hV.isGlobular
    have gW := hW.isGlobular
    have fV := homOfLe_cond_mem_saturation_of_isPastingIn U false hp (ihW i false) hp.left_le
    have fW := homOfLe_cond_mem_saturation_of_isPastingIn U true hp (ihV i true) hp.right_le
    have key : ∀ (F : LowerSet U.ogp) (hF : F ≤ B), U.ogp.boundary B k α = U.ogp.boundary F k α →
        MorphismProperty.saturation.{u} hornInclusions.{u}
          (Subfunctor.homOfLe (closedSubpresheaf_mono U (boundary_le F k α))) →
        MorphismProperty.saturation.{u} hornInclusions.{u}
          (Subfunctor.homOfLe (closedSubpresheaf_mono U hF)) →
        MorphismProperty.saturation.{u} hornInclusions.{u}
          (Subfunctor.homOfLe (closedSubpresheaf_mono U (boundary_le B k α))) :=
      fun F hF hb ihF fF => homOfLe_mem_saturation_of_eq_left U (boundary_le B k α)
        ((boundary_le F k α).trans hF) hb (homOfLe_mem_saturation_trans U (boundary_le F k α) hF
          ((boundary_le F k α).trans hF) ihF fF)
    rcases lt_trichotomy k i with hki | rfl | hik
    · exact key V hp.left_le (hp.boundary_eq_of_lt_cond false gW gV hki α) (ihV k α) fV
    · cases α
      exacts [key V hp.left_le hp.boundary_input (ihV _ _) fV,
        key W hp.right_le hp.boundary_output (ihW _ _) fW]
    · exact homOfLe_boundary_mem_saturation_of_isPastingIn_of_lt U hp gV gW hik α
        (ihV k α) (ihW k α) (boundary_le B k α)

theorem homOfLe_mem_saturation_of_isSubmoleculeOf (U : Atom) {S T : LowerSet U.ogp}
    (h : IsSubmoleculeOf U.ogp S T) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U h.le)) := by
  have key : ∀ {Y T : LowerSet U.ogp}, Relation.ReflTransGen U.ogp.IsPastingFactorOf Y T →
      ∀ (hYT : Y ≤ T), MorphismProperty.saturation.{u} hornInclusions.{u}
        (Subfunctor.homOfLe (closedSubpresheaf_mono U hYT)) := by
    intro Y T hrt
    induction hrt with
    | refl => exact fun hYY => homOfLe_mem_saturation_of_eq U hYY rfl
    | @tail Z W hYZ hZW ih =>
      intro hYW
      have hYZ' : Y ≤ Z := (IsSubmoleculeOf.le ⟨hZW.isMoleculeIn_left, hYZ⟩)
      obtain ⟨k, α, X, hp, _, hX⟩ := hZW
      have hZW' : Z ≤ W := ((isPastingIn_cond_iff α).1 hp).1 ▸ le_sup_right
      exact homOfLe_mem_saturation_trans U hYZ' hZW' hYW (ih hYZ')
        (homOfLe_cond_mem_saturation_of_isPastingIn U α hp
          (homOfLe_boundary_mem_saturation U hX k α) hZW')
  exact key h.2 h.le

theorem yoneda_map_closureIncl_mem_saturation (U : Atom) (x : U.ogp) :
    MorphismProperty.saturation.{u} hornInclusions.{u}
      (uliftYoneda.{u}.map (Atom.closureIncl U x)) := by
  have hf := Atom.isInclusionHom_closureIncl U x
  have hP : IsIso (closedSubpresheaf (Atom.ofClosure U x) ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (closedSubpresheaf_univ _)
  have hU : IsIso (closedSubpresheaf U ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (closedSubpresheaf_univ _)
  have hsub : Atom.map (Atom.closureIncl U x) ⊤ ≤ ⊤ := le_top
  have hm : MorphismProperty.saturation.{u} hornInclusions.{u}
      (Subfunctor.homOfLe (closedSubpresheaf_mono U hsub)) := by
    refine homOfLe_mem_saturation_of_eq_left U hsub (le_top : LowerSet.Iic x ≤ ⊤)
      (Atom.map_closureInclOGP_top U x) ?_
    exact homOfLe_mem_saturation_of_isSubmoleculeOf U
      (U.isMolecule.Iic_isSubmoleculeOf LowerSet.mem_top)
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk
    ((closedSubpresheafImageIso (Atom.closureIncl U x) hf ⊤).symm ≪≫
      @asIso _ _ _ _ (closedSubpresheaf (Atom.ofClosure U x) ⊤).ι hP)
    (@asIso _ _ _ _ (closedSubpresheaf U ⊤).ι hU) ?_)).1 hm
  change ((closedSubpresheafImageIso (Atom.closureIncl U x) hf ⊤).inv ≫
      (closedSubpresheaf (Atom.ofClosure U x) ⊤).ι) ≫ uliftYoneda.{u}.map (Atom.closureIncl U x)
    = Subfunctor.homOfLe (closedSubpresheaf_mono U hsub) ≫ (closedSubpresheaf U ⊤).ι
  have key : (closedSubpresheafImageIso (Atom.closureIncl U x) hf ⊤).inv ≫
      (closedSubpresheaf (Atom.ofClosure U x) ⊤).ι ≫ uliftYoneda.{u}.map (Atom.closureIncl U x)
      = (closedSubpresheaf U (Atom.map (Atom.closureIncl U x) ⊤)).ι := by
    rw [← closedSubpresheafImageIso_hom_comp_ι (Atom.closureIncl U x) hf ⊤]
    exact Iso.inv_hom_id_assoc _ _
  rw [Subfunctor.homOfLe_ι]
  exact (Category.assoc _ _ _).trans key

theorem yoneda_map_mem_saturation_hornInclusions {V U : Atom} (f : V ⟶ U)
    (hf : IsInclusionHom f) :
    MorphismProperty.saturation.{u} hornInclusions.{u} (uliftYoneda.{u}.map f) := by
  have hL := isIso_principalLift_of_isInclusionHom f hf
  rw [← principalLift_comp_closureIncl U (f V.top) f (apply_mem_closure_apply_top f),
    Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.isomorphisms_le_of_containsIdentities _ _
      (MorphismProperty.isomorphisms.infer_property _))
    (yoneda_map_closureIncl_mem_saturation U _)

end Atoms.Diagrammatic
