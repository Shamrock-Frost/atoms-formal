import Atoms.Diagrammatic.Limits.Cone

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {K K' X : DiagSet.{u}}

theorem homEquiv_symm_comp_grayHomRestrict {A B T Z : DiagSet.{u}} (i : A ⟶ B)
    (s : T ⟶ (grayHomRight B).obj Z) :
    ((grayTensorRightAdjunction A).homEquiv T Z).symm (s ≫ (grayHomRestrict i).app Z) =
      (grayTensorLeft T).map i ≫ ((grayTensorRightAdjunction B).homEquiv T Z).symm s := by
  rw [Equiv.symm_apply_eq, ← homEquiv_comp_grayHomRestrict, Equiv.apply_symm_apply]

@[reassoc]
theorem constDiagram_comp_grayHomRestrict (k : K' ⟶ K) (X : DiagSet.{u}) :
    constDiagram K X ≫ (grayHomRestrict k).app X = constDiagram K' X := by
  rw [constDiagram, constDiagram, homEquiv_comp_grayHomRestrict, grayTensorLeft_map_eq,
    grayTensorBifunctor_map_grayTensorFst, Category.comp_id]

@[reassoc]
theorem diagramPoint_comp_grayHomRestrict (k : K' ⟶ K) (d : K ⟶ X) :
    diagramPoint d ≫ (grayHomRestrict k).app X = diagramPoint (k ≫ d) := by
  rw [diagramPoint, diagramPoint, homEquiv_comp_grayHomRestrict,
    reassoc_of% grayTensorLeft_map_grayTensorSnd]

@[reassoc]
theorem coneObjectBase_comp_grayHomRestrict (α : Bool) (k : K' ⟶ K) {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') :
    coneObjectBase α d ≫ (grayHomRight intervalBoundary.{u}).map ((grayHomRestrict k).app X) =
      coneObjectBase α d' := by
  subst h
  rw [coneObjectBase, coneObjectBase, boundaryHom_comp]
  cases α <;> simp only [cond, constDiagram_comp_grayHomRestrict, Category.assoc,
    diagramPoint_comp_grayHomRestrict]

noncomputable def coneObjectRestrict (α : Bool) (k : K' ⟶ K) {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') : coneObject α d ⟶ coneObject α d' :=
  pullback.map _ _ _ _ ((grayHomRight (ball.{u} (atomSimplex 1))).map ((grayHomRestrict k).app X))
    (𝟙 X) ((grayHomRight intervalBoundary.{u}).map ((grayHomRestrict k).app X))
    ((grayHomRestrict intervalBoundaryι).naturality _).symm
    ((coneObjectBase_comp_grayHomRestrict α k h).trans (Category.id_comp _).symm)

@[reassoc (attr := simp)]
theorem coneObjectRestrict_π (α : Bool) (k : K' ⟶ K) {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') :
    coneObjectRestrict α k h ≫ coneObjectπ α d' = coneObjectπ α d :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem coneObjectRestrict_ι (α : Bool) (k : K' ⟶ K) {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') :
    coneObjectRestrict α k h ≫ coneObjectι α d' =
      coneObjectι α d ≫ (grayHomRight (ball.{u} (atomSimplex 1))).map ((grayHomRestrict k).app X) :=
  pullback.lift_fst _ _ _

theorem coneObjectRestrict_id (α : Bool) (d : K ⟶ X) :
    coneObjectRestrict α (𝟙 K) (Category.id_comp d) = 𝟙 _ :=
  coneObject_hom_ext (by simp) (by simp)

theorem coneObjectRestrict_comp (α : Bool) {K'' : DiagSet.{u}} (k : K'' ⟶ K') (k' : K' ⟶ K)
    {d : K ⟶ X} {d' : K' ⟶ X} {d'' : K'' ⟶ X} (h : k' ≫ d = d') (h' : k ≫ d' = d'') :
    coneObjectRestrict α k' h ≫ coneObjectRestrict α k h' =
      coneObjectRestrict α (k ≫ k') (by rw [Category.assoc, h, h']) :=
  coneObject_hom_ext (by simp [grayHomRestrict_comp]) (by simp)

instance isIso_coneObjectRestrict (α : Bool) (k : K' ⟶ K) [IsIso k] {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') : IsIso (coneObjectRestrict α k h) := by
  have e {L : DiagSet.{u}} {e : L ⟶ X} (k₀ : L ⟶ L) (hk : k₀ = 𝟙 L) (h₀ : k₀ ≫ e = e) :
      coneObjectRestrict α k₀ h₀ = 𝟙 _ := by
    subst hk
    exact coneObjectRestrict_id α e
  have hinv : inv k ≫ d' = d := by rw [← h, IsIso.inv_hom_id_assoc]
  exact ⟨coneObjectRestrict α (inv k) hinv,
    by rw [coneObjectRestrict_comp, e _ (IsIso.inv_hom_id k)],
    by rw [coneObjectRestrict_comp, e _ (IsIso.hom_inv_id k)]⟩

theorem isPullback_grayHomRestrict {K₀ K₁ K₂ : DiagSet.{u}} {k₁ : K₀ ⟶ K₁} {k₂ : K₀ ⟶ K₂}
    {j₁ : K₁ ⟶ K} {j₂ : K₂ ⟶ K} (hK : IsPushout k₁ k₂ j₁ j₂) (X : DiagSet.{u}) :
    IsPullback ((grayHomRestrict j₁).app X) ((grayHomRestrict j₂).app X)
      ((grayHomRestrict k₁).app X) ((grayHomRestrict k₂).app X) := by
  have w : (grayHomRestrict j₁).app X ≫ (grayHomRestrict k₁).app X =
      (grayHomRestrict j₂).app X ≫ (grayHomRestrict k₂).app X := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← grayHomRestrict_comp, ← grayHomRestrict_comp,
      hK.w]
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w (fun s => ?_) ?_ ?_ ?_)
  · exact (grayTensorRightAdjunction K).homEquiv _ X ((hK.map (grayTensorLeft s.pt)).desc
      (((grayTensorRightAdjunction K₁).homEquiv _ X).symm s.fst)
      (((grayTensorRightAdjunction K₂).homEquiv _ X).symm s.snd)
      (by rw [← homEquiv_symm_comp_grayHomRestrict, ← homEquiv_symm_comp_grayHomRestrict,
        s.condition]))
  · intro s
    rw [homEquiv_comp_grayHomRestrict, IsPushout.inl_desc, Equiv.apply_symm_apply]
  · intro s
    rw [homEquiv_comp_grayHomRestrict, IsPushout.inr_desc, Equiv.apply_symm_apply]
  · intro s m h₁ h₂
    rw [← Equiv.symm_apply_eq]
    refine (hK.map (grayTensorLeft s.pt)).hom_ext ?_ ?_
    · rw [IsPushout.inl_desc, ← h₁, homEquiv_symm_comp_grayHomRestrict]
    · rw [IsPushout.inr_desc, ← h₂, homEquiv_symm_comp_grayHomRestrict]

section Glued

variable {K₀ K₁ K₂ : DiagSet.{u}} {k₁ : K₀ ⟶ K₁} {k₂ : K₀ ⟶ K₂} {j₁ : K₁ ⟶ K} {j₂ : K₂ ⟶ K}
  {d : K ⟶ X} {d₀ : K₀ ⟶ X} {d₁ : K₁ ⟶ X} {d₂ : K₂ ⟶ X}

private theorem coneObjectRestrict_lift_w (α : Bool) (hK : IsPushout k₁ k₂ j₁ j₂)
    (h₁ : j₁ ≫ d = d₁) (h₂ : j₂ ≫ d = d₂) {T : DiagSet.{u}} (a : T ⟶ coneObject α d₁)
    (b : T ⟶ coneObject α d₂)
    (m : T ⟶ (grayHomRight (ball.{u} (atomSimplex 1))).obj ((grayHomRight K).obj X))
    (ha : m ≫ (grayHomRight _).map ((grayHomRestrict j₁).app X) = a ≫ coneObjectι α d₁)
    (hb : m ≫ (grayHomRight _).map ((grayHomRestrict j₂).app X) = b ≫ coneObjectι α d₂)
    (hπ : a ≫ coneObjectπ α d₁ = b ≫ coneObjectπ α d₂) :
    m ≫ (grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X) =
      (a ≫ coneObjectπ α d₁) ≫ coneObjectBase α d := by
  have := (grayTensorRightAdjunction intervalBoundary.{u}).rightAdjoint_preservesLimits
  refine ((isPullback_grayHomRestrict hK X).map (grayHomRight intervalBoundary.{u})).hom_ext ?_ ?_
  · rw [Category.assoc, ← (grayHomRestrict intervalBoundaryι).naturality, reassoc_of% ha,
      Category.assoc, Category.assoc, coneObjectBase_comp_grayHomRestrict α j₁ h₁,
      (isPullback_coneObject α d₁).w]
  · rw [Category.assoc, ← (grayHomRestrict intervalBoundaryι).naturality, reassoc_of% hb,
      Category.assoc, Category.assoc, coneObjectBase_comp_grayHomRestrict α j₂ h₂,
      reassoc_of% hπ, (isPullback_coneObject α d₂).w]

private theorem coneObjectRestrict_hom_ext (α : Bool) (hK : IsPushout k₁ k₂ j₁ j₂)
    (h₁ : j₁ ≫ d = d₁) (h₂ : j₂ ≫ d = d₂) {T : DiagSet.{u}} {f g : T ⟶ coneObject α d}
    (e₁ : f ≫ coneObjectRestrict α j₁ h₁ = g ≫ coneObjectRestrict α j₁ h₁)
    (e₂ : f ≫ coneObjectRestrict α j₂ h₂ = g ≫ coneObjectRestrict α j₂ h₂) : f = g := by
  have := (grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).rightAdjoint_preservesLimits
  refine coneObject_hom_ext (((isPullback_grayHomRestrict hK X).map
    (grayHomRight (ball.{u} (atomSimplex 1)))).hom_ext ?_ ?_) ?_
  · simpa only [Category.assoc, coneObjectRestrict_ι] using congrArg (· ≫ coneObjectι α d₁) e₁
  · simpa only [Category.assoc, coneObjectRestrict_ι] using congrArg (· ≫ coneObjectι α d₂) e₂
  · simpa only [Category.assoc, coneObjectRestrict_π] using congrArg (· ≫ coneObjectπ α d₁) e₁

theorem isPullback_coneObjectRestrict_of_eq (α : Bool) (hK : IsPushout k₁ k₂ j₁ j₂)
    (h₁ : j₁ ≫ d = d₁) (h₂ : j₂ ≫ d = d₂) (h₀₁ : k₁ ≫ d₁ = d₀) (h₀₂ : k₂ ≫ d₂ = d₀) :
    IsPullback (coneObjectRestrict α j₁ h₁) (coneObjectRestrict α j₂ h₂)
      (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂) := by
  have := (grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).rightAdjoint_preservesLimits
  have hI := (isPullback_grayHomRestrict hK X).map (grayHomRight (ball.{u} (atomSimplex 1)))
  have w : coneObjectRestrict α j₁ h₁ ≫ coneObjectRestrict α k₁ h₀₁ =
      coneObjectRestrict α j₂ h₂ ≫ coneObjectRestrict α k₂ h₀₂ := by
    rw [coneObjectRestrict_comp, coneObjectRestrict_comp]
    congr 1
    exact hK.w
  have hπ (s : PullbackCone (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂)) :
      s.fst ≫ coneObjectπ α d₁ = s.snd ≫ coneObjectπ α d₂ := by
    rw [← coneObjectRestrict_π α k₁ h₀₁, reassoc_of% s.condition, coneObjectRestrict_π]
  have hι (s : PullbackCone (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂)) :
      (s.fst ≫ coneObjectι α d₁) ≫ (grayHomRight _).map ((grayHomRestrict k₁).app X) =
        (s.snd ≫ coneObjectι α d₂) ≫ (grayHomRight _).map ((grayHomRestrict k₂).app X) := by
    rw [Category.assoc, Category.assoc, ← coneObjectRestrict_ι α k₁ h₀₁,
      ← coneObjectRestrict_ι α k₂ h₀₂, reassoc_of% s.condition]
  let l (s : PullbackCone (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂)) :
      s.pt ⟶ coneObject α d :=
    (isPullback_coneObject α d).lift (hI.lift _ _ (hι s)) (s.fst ≫ coneObjectπ α d₁)
      (coneObjectRestrict_lift_w α hK h₁ h₂ s.fst s.snd _ (hI.lift_fst _ _ _)
        (hI.lift_snd _ _ _) (hπ s))
  have fac₁ (s : PullbackCone (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂)) :
      l s ≫ coneObjectRestrict α j₁ h₁ = s.fst := by
    refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, coneObjectRestrict_ι]
      exact (IsPullback.lift_fst_assoc _ _ _ _ _).trans (hI.lift_fst _ _ _)
    · rw [Category.assoc, coneObjectRestrict_π]
      exact IsPullback.lift_snd _ _ _ _
  have fac₂ (s : PullbackCone (coneObjectRestrict α k₁ h₀₁) (coneObjectRestrict α k₂ h₀₂)) :
      l s ≫ coneObjectRestrict α j₂ h₂ = s.snd := by
    refine coneObject_hom_ext ?_ ?_
    · rw [Category.assoc, coneObjectRestrict_ι]
      exact (IsPullback.lift_fst_assoc _ _ _ _ _).trans (hI.lift_snd _ _ _)
    · rw [Category.assoc, coneObjectRestrict_π]
      exact (IsPullback.lift_snd _ _ _ _).trans (hπ s)
  exact IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w l fac₁ fac₂ fun s m hm₁ hm₂ =>
    coneObjectRestrict_hom_ext α hK h₁ h₂ (hm₁.trans (fac₁ s).symm) (hm₂.trans (fac₂ s).symm))

end Glued

theorem isPullback_coneObjectRestrict (α : Bool) {K₀ K₁ K₂ : DiagSet.{u}} {k₁ : K₀ ⟶ K₁}
    {k₂ : K₀ ⟶ K₂} {j₁ : K₁ ⟶ K} {j₂ : K₂ ⟶ K} (hK : IsPushout k₁ k₂ j₁ j₂) (d : K ⟶ X) :
    IsPullback (coneObjectRestrict α j₁ (d' := j₁ ≫ d) rfl)
      (coneObjectRestrict α j₂ (d' := j₂ ≫ d) rfl)
      (coneObjectRestrict α k₁ (d' := k₁ ≫ j₁ ≫ d) rfl)
      (coneObjectRestrict α k₂ (d' := k₁ ≫ j₁ ≫ d)
        (by rw [← Category.assoc, ← hK.w, Category.assoc])) :=
  isPullback_coneObjectRestrict_of_eq α hK rfl rfl rfl _

theorem isPullback_coneObjectRestrict_coprod (α : Bool) {K₁ K₂ : DiagSet.{u}} (d₁ : K₁ ⟶ X)
    (d₂ : K₂ ⟶ X) :
    IsPullback (coneObjectRestrict α (coprod.inl (X := K₁) (Y := K₂)) (coprod.inl_desc d₁ d₂))
      (coneObjectRestrict α (coprod.inr (X := K₁) (Y := K₂)) (coprod.inr_desc d₁ d₂))
      (coneObjectπ α d₁) (coneObjectπ α d₂) := by
  have h := isPullback_coneObjectRestrict_of_eq α (IsPushout.of_hasBinaryCoproduct' K₁ K₂)
    (coprod.inl_desc d₁ d₂) (coprod.inr_desc d₁ d₂) (initial.hom_ext _ (initial.to X))
    (initial.hom_ext _ (initial.to X))
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (coneObjectπ α (initial.to X)))
    ?_ ?_ ?_ ?_ <;> simp

end Atoms.Diagrammatic
