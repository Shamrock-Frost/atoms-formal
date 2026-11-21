import Atoms.ForMathlib.CategoryTheory.Presentable.Presheaf
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic
import Atoms.Homotopical.EilenbergZilber.Normal
import Atoms.Homotopical.EilenbergZilber.RigidCellularModel

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical.EZCategory

universe w v

variable {A : Type v} [SmallCategory A] [EZCategory A] {Y : Aᵒᵖ ⥤ Type (max w v)}

section Saturation

theorem saturation_boundaryInclusions_ι_of_normalMonomorphisms (R : Subfunctor Y)
    (hR : normalMonomorphisms A R.ι) : saturation.{max w v} (boundaryInclusions.{w} A) R.ι :=
  (isUnionChain_cellChain R).ι_mem (cellChain_top R) _ fun q ↦
    MorphismProperty.of_isPushout (isPushout_boundaryInclusion_of_dominant q
      ((normalMonomorphisms_ι_iff R).1 hR _ (rep q).isNondegenerate (rep q).not_mem))
      (le_saturation.{max w v} _ _ (MorphismProperty.ofHoms.mk (rep q).obj))

theorem normalMonomorphisms_eq_saturation_boundaryInclusions :
    (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) =
      saturation.{max w v} (boundaryInclusions.{w} A) := by
  refine le_antisymm (fun X Z i hi ↦ ?_) (saturation_le _ _ ?_)
  · have := hi.1
    rw [← Subfunctor.toRange_ι i]
    refine MorphismProperty.comp_mem _ _ _ (isomorphisms_le_of_containsIdentities _ _
      (MorphismProperty.isomorphisms.infer_property _))
      (saturation_boundaryInclusions_ι_of_normalMonomorphisms _ ?_)
    exact (normalMonomorphisms_ι_iff _).2 fun _ y hy hyR ↦ hi.2 y hy hyR
  · rintro _ _ _ ⟨a⟩
    exact normalMonomorphisms_of_isNormal _ (isNormal_uliftYoneda a)

theorem tfae_hasTrivialAutomorphisms :
    List.TFAE
      [∀ X : Aᵒᵖ ⥤ Type (max w v), IsNormal X,
       (normalMonomorphisms A : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) =
         MorphismProperty.monomorphisms _,
       saturation.{max w v} (boundaryInclusions.{w} A) = MorphismProperty.monomorphisms _,
       (boundaryInclusions.{w} A).rlp.llp = MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)),
       HasTrivialAutomorphisms A] := by
  have : (boundaryInclusions.{w} A).IsSmall.{max w v} := isSmall_ofHoms.{max w v} _
  tfae_have 1 → 2 := fun h ↦ le_antisymm normalMonomorphisms_le_monomorphisms
    fun _ Z i (hi : Mono i) ↦ normalMonomorphisms_of_isNormal i (h Z)
  tfae_have 2 → 1 := fun h X ↦ by
    have hbot : normalMonomorphisms A (⊥ : Subfunctor X).ι := by
      rw [h]
      exact MorphismProperty.monomorphisms.infer_property _
    exact fun _ y hy ↦ (normalMonomorphisms_ι_iff _).1 hbot y hy (Set.notMem_empty y)
  tfae_have 2 ↔ 3 := by rw [normalMonomorphisms_eq_saturation_boundaryInclusions]
  tfae_have 3 ↔ 4 := by rw [saturation_eq_llp_rlp]
  tfae_have 5 → 1 := fun _ ↦ isNormal_of_hasTrivialAutomorphisms
  tfae_have 1 → 5 := hasTrivialAutomorphisms_of_forall_isNormal.{w}
  tfae_finish

end Saturation

omit [EZCategory A] in
theorem sigma_map_uliftBoundary_ι_app_ι_app {ι : Type (max w v)} (o : ι → A) (c : ι) {b : Aᵒᵖ}
    (f : (uliftBoundary.{w} (o c)).toFunctor.obj b) :
    (Limits.Sigma.map fun c ↦ (uliftBoundary.{w} (o c)).ι).app b
      ((Sigma.ι (fun c ↦ (uliftBoundary.{w} (o c)).toFunctor) c).app b f) =
      (Sigma.ι (fun c ↦ uliftYoneda.{w}.obj (o c)) c).app b f.val :=
  congrArg (fun φ : (uliftBoundary.{w} (o c)).toFunctor ⟶ ∐ fun c ↦ uliftYoneda.{w}.obj (o c) ↦
    φ.app b f) (Sigma.ι_map (fun c ↦ (uliftBoundary.{w} (o c)).ι) c)

omit [EZCategory A] in
theorem exists_sigma_ι_app_eq {ι : Type (max w v)} (o : ι → A) {b : Aᵒᵖ}
    (y : (∐ fun c ↦ uliftYoneda.{w}.obj (o c)).obj b) :
    ∃ (c : ι) (f : (uliftYoneda.{w}.obj (o c)).obj b),
      (Sigma.ι (fun c ↦ uliftYoneda.{w}.obj (o c)) c).app b f = y :=
  Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj b) _ _ (coproductIsCoproduct _)) y

omit [EZCategory A] in
theorem exists_isSplitEpi_sigma_ι_app_eq {ι : Type (max w v)} (o : ι → A) {b : Aᵒᵖ}
    (y : (∐ fun c ↦ uliftYoneda.{w}.obj (o c)).obj b)
    (hy : y ∉ Set.range ((Limits.Sigma.map fun c ↦ (uliftBoundary.{w} (o c)).ι).app b)) :
    ∃ (c : ι) (f : (uliftYoneda.{w}.obj (o c)).obj b),
      IsSplitEpi f.down ∧ (Sigma.ι (fun c ↦ uliftYoneda.{w}.obj (o c)) c).app b f = y := by
  obtain ⟨c, f, rfl⟩ := exists_sigma_ι_app_eq o y
  exact ⟨c, f, by_contra fun hf ↦ hy ⟨_, sigma_map_uliftBoundary_ι_app_ι_app o c ⟨f, hf⟩⟩, rfl⟩

section RelativeSkeleton

def relativeSkeleton (R : Subfunctor Y) : ℕ → Subfunctor Y
  | 0 => R
  | n + 1 => R ⊔ skeletonSubfunctor n Y

variable (R : Subfunctor Y)

theorem relativeSkeleton_zero : relativeSkeleton R 0 = R :=
  rfl

theorem relativeSkeleton_succ (n : ℕ) :
    relativeSkeleton R (n + 1) = R ⊔ skeletonSubfunctor n Y :=
  rfl

theorem le_relativeSkeleton (n : ℕ) : R ≤ relativeSkeleton R n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left

theorem relativeSkeleton_monotone : Monotone (relativeSkeleton R) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  cases n with
  | zero => exact le_sup_left
  | succ n => exact sup_le_sup_left (skeletonSubfunctor_monotone Y n.le_succ) R

variable {R} in
theorem map_mem_relativeSkeleton_of_deg_lt {n : ℕ} {b c : A} (f : b ⟶ c) (y : Y.obj (op c))
    (hc : deg c < n) : Y.map f.op y ∈ (relativeSkeleton R n).obj (op b) := by
  cases n with
  | zero => exact absurd hc (Nat.not_lt_zero _)
  | succ n => exact Or.inr (map_mem_skeletonSubfunctor f y (Nat.lt_succ_iff.1 hc))

theorem iSup_relativeSkeleton : ⨆ n, relativeSkeleton R n = ⊤ := by
  refine eq_top_iff.2 fun b x _ ↦ ?_
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  have h := map_mem_relativeSkeleton_of_deg_lt (R := R) (𝟙 b.unop) x (Nat.lt_succ_self _)
  rw [op_id, Functor.map_id_apply] at h
  exact ⟨_, h⟩

def RelativeSkeletonCell (R : Subfunctor Y) (n : ℕ) : Type (max w v) :=
  {q : CellClass R // cellDeg q = n}

variable {R}

theorem range_le_relativeSkeleton_succ {n : ℕ} (c : RelativeSkeletonCell R n) :
    Subfunctor.range (uliftYonedaEquiv.symm (rep c.val).cell) ≤ relativeSkeleton R (n + 1) := by
  rintro b _ ⟨f, rfl⟩
  exact Or.inr (map_mem_skeletonSubfunctor f.down (rep c.val).cell c.property.le)

theorem range_uliftBoundary_ι_comp_le_relativeSkeleton {n : ℕ} (c : RelativeSkeletonCell R n) :
    Subfunctor.range ((uliftBoundary.{w} (rep c.val).obj).ι ≫
      uliftYonedaEquiv.symm (rep c.val).cell) ≤ relativeSkeleton R n := by
  rintro b _ ⟨⟨f, hf⟩, rfl⟩
  obtain ⟨c₁, p, i, hp, hi, hpi⟩ := exists_factorization f.down
  have hlt : deg c₁ < n := by
    refine c.property ▸ lt_of_le_of_ne (deg_le_of_mono i hi) fun he ↦ hf ?_
    have := isIso_of_mono_of_deg_eq i hi he
    rw [← hpi]
    infer_instance
  change Y.map f.down.op (rep c.val).cell ∈ _
  rw [← hpi, op_comp, Functor.map_comp_apply]
  exact map_mem_relativeSkeleton_of_deg_lt p _ hlt

variable (R) (n : ℕ)

noncomputable def relativeSkeletonPushoutTop :
    (∐ fun c : RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).toFunctor) ⟶
      (relativeSkeleton R n).toFunctor :=
  Sigma.desc fun c ↦ Subfunctor.lift _ (range_uliftBoundary_ι_comp_le_relativeSkeleton c)

noncomputable def relativeSkeletonPushoutBottom :
    (∐ fun c : RelativeSkeletonCell R n ↦ uliftYoneda.{w}.obj (rep c.val).obj) ⟶
      (relativeSkeleton R (n + 1)).toFunctor :=
  Sigma.desc fun c ↦ Subfunctor.lift _ (range_le_relativeSkeleton_succ c)

variable {R n}

theorem relativeSkeletonPushoutBottom_app_ι_app (c : RelativeSkeletonCell R n) {b : Aᵒᵖ}
    (f : (uliftYoneda.{w}.obj (rep c.val).obj).obj b) :
    ((relativeSkeletonPushoutBottom R n).app b ((Sigma.ι (fun c : RelativeSkeletonCell R n ↦
      uliftYoneda.{w}.obj (rep c.val).obj) c).app b f)).val =
      Y.map f.down.op (rep c.val).cell :=
  congrArg Subtype.val (congrArg (fun φ ↦ φ.app b f) (Sigma.ι_desc (f := fun c :
    RelativeSkeletonCell R n ↦ uliftYoneda.{w}.obj (rep c.val).obj) (fun c ↦ Subfunctor.lift _
      (range_le_relativeSkeleton_succ c)) c))

private theorem relativeSkeletonPushoutTop_app_ι_app (c : RelativeSkeletonCell R n) {b : Aᵒᵖ}
    (f : (uliftBoundary.{w} (rep c.val).obj).toFunctor.obj b) :
    ((relativeSkeletonPushoutTop R n).app b ((Sigma.ι (fun c : RelativeSkeletonCell R n ↦
      (uliftBoundary.{w} (rep c.val).obj).toFunctor) c).app b f)).val =
      Y.map f.val.down.op (rep c.val).cell :=
  congrArg Subtype.val (congrArg (fun φ ↦ φ.app b f) (Sigma.ι_desc (f := fun c :
    RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).toFunctor) (fun c ↦
      Subfunctor.lift _ (range_uliftBoundary_ι_comp_le_relativeSkeleton c)) c))

theorem map_not_mem_relativeSkeleton_of_isSplitEpi (c : RelativeSkeletonCell R n) {b : A}
    (p : b ⟶ (rep c.val).obj) [IsSplitEpi p] :
    Y.map p.op (rep c.val).cell ∉ (relativeSkeleton R n).obj (op b) := by
  have hR : Y.map p.op (rep c.val).cell ∉ R.obj (op b) := fun h ↦ by
    have h' : Y.map (section_ p).op (Y.map p.op (rep c.val).cell) ∈ R.obj (op (rep c.val).obj) :=
      R.map (section_ p).op h
    rw [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h'
    exact (rep c.val).not_mem h'
  cases n with
  | zero => exact hR
  | succ n =>
    rintro (h | h)
    · exact hR h
    · have hc := (mem_skeletonSubfunctor_iff_of_isNondegenerate (rep c.val).isNondegenerate).1
        ((map_mem_skeletonSubfunctor_iff_of_isSplitEpi p _).1 h)
      have hdeg : deg (rep c.val).obj = n + 1 := c.property
      omega

variable (R n)

theorem relativeSkeletonPushout_w :
    relativeSkeletonPushoutTop R n ≫ Subfunctor.homOfLe (relativeSkeleton_monotone R n.le_succ) =
      Limits.Sigma.map (fun c : RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).ι) ≫
        relativeSkeletonPushoutBottom R n := by
  ext c : 1
  simp [relativeSkeletonPushoutTop, relativeSkeletonPushoutBottom,
    ← cancel_mono (Subfunctor.ι _)]

theorem isPullback_relativeSkeleton :
    IsPullback (relativeSkeletonPushoutTop R n)
      (Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).ι)
      (Subfunctor.homOfLe (relativeSkeleton_monotone R n.le_succ))
      (relativeSkeletonPushoutBottom R n) :=
  IsPullback.of_forall_isPullback_app fun b ↦ by
    rw [Types.isPullback_iff]
    refine ⟨congrArg (fun φ ↦ φ.app b) (relativeSkeletonPushout_w R n),
      fun x₁ x₂ ⟨_, h⟩ ↦ injective_of_mono ((Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦
        (uliftBoundary.{w} (rep c.val).obj).ι).app b) h, fun ⟨x, hx⟩ y h ↦ ?_⟩
    obtain ⟨c, f, rfl⟩ :=
      exists_sigma_ι_app_eq.{w} (fun c : RelativeSkeletonCell R n ↦ (rep c.val).obj) y
    have hval : x = Y.map f.down.op (rep c.val).cell :=
      (congrArg Subtype.val h).trans (relativeSkeletonPushoutBottom_app_ι_app c f)
    have hf : ¬IsSplitEpi f.down := fun hf ↦
      map_not_mem_relativeSkeleton_of_isSplitEpi c f.down (hval ▸ hx)
    exact ⟨(Sigma.ι (fun c : RelativeSkeletonCell R n ↦
      (uliftBoundary.{w} (rep c.val).obj).toFunctor) c).app b ⟨f, hf⟩,
      Subtype.ext ((relativeSkeletonPushoutTop_app_ι_app c ⟨f, hf⟩).trans hval.symm),
      sigma_map_uliftBoundary_ι_app_ι_app.{w} (fun c : RelativeSkeletonCell R n ↦ (rep c.val).obj)
        c ⟨f, hf⟩⟩

private theorem range_union_range_relativeSkeletonPushoutBottom (b : Aᵒᵖ) :
    Set.range ((Subfunctor.homOfLe (relativeSkeleton_monotone R n.le_succ)).app b) ⊔
      Set.range ((relativeSkeletonPushoutBottom R n).app b) = Set.univ := by
  refine Set.eq_univ_of_forall fun ⟨x, hx⟩ ↦ ?_
  obtain ⟨c, p, z, hp, hz, rfl⟩ := exists_isNondegenerate Y b.unop x
  have := hp
  rcases hx with hx | hx
  · exact Or.inl ⟨⟨_, le_relativeSkeleton R n _ hx⟩, rfl⟩
  have hc : deg c ≤ n := (mem_skeletonSubfunctor_iff_of_isNondegenerate hz).1
    ((map_mem_skeletonSubfunctor_iff_of_isSplitEpi p z).1 hx)
  rcases hc.lt_or_eq with hc | hc
  · exact Or.inl ⟨⟨_, map_mem_relativeSkeleton_of_deg_lt p z hc⟩, rfl⟩
  by_cases hzR : z ∈ R.obj (op c)
  · exact Or.inl ⟨⟨_, le_relativeSkeleton R n _ (R.map p.op hzR)⟩, rfl⟩
  let z' : NondegenerateCell R := ⟨c, z, hz, hzR⟩
  let q : RelativeSkeletonCell R n := ⟨cellMk z', (cellDeg_cellMk z').trans hc⟩
  obtain ⟨e, he⟩ := exists_iso_rep_cellMk z'
  refine Or.inr ⟨(Sigma.ι (fun c : RelativeSkeletonCell R n ↦
    uliftYoneda.{w}.obj (rep c.val).obj) q).app b ⟨p ≫ e.inv⟩, Subtype.ext ?_⟩
  refine (relativeSkeletonPushoutBottom_app_ι_app q _).trans ?_
  change Y.map (p ≫ e.inv).op (rep (cellMk z')).cell = Y.map p.op z
  rw [← he, ← Functor.map_comp_apply, ← op_comp, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem relativeSkeletonPushoutBottom_injective
    (hR : ∀ (a : A) (x : Y.obj (op a)), deg a = n → IsNondegenerate Y x →
      x ∉ R.obj (op a) → IsDominant x)
    {b : Aᵒᵖ} (y₁ y₂ : (∐ fun c : RelativeSkeletonCell R n ↦
      uliftYoneda.{w}.obj (rep c.val).obj).obj b)
    (hy₁ : y₁ ∉ Set.range ((Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦
      (uliftBoundary.{w} (rep c.val).obj).ι).app b))
    (hy₂ : y₂ ∉ Set.range ((Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦
      (uliftBoundary.{w} (rep c.val).obj).ι).app b))
    (h : (relativeSkeletonPushoutBottom R n).app b y₁ =
      (relativeSkeletonPushoutBottom R n).app b y₂) :
    y₁ = y₂ := by
  obtain ⟨c₁, f₁, hf₁, rfl⟩ := exists_isSplitEpi_sigma_ι_app_eq.{w}
    (fun c : RelativeSkeletonCell R n ↦ (rep c.val).obj) y₁ hy₁
  obtain ⟨c₂, f₂, hf₂, rfl⟩ := exists_isSplitEpi_sigma_ι_app_eq.{w}
    (fun c : RelativeSkeletonCell R n ↦ (rep c.val).obj) y₂ hy₂
  have h' := congrArg Subtype.val h
  rw [relativeSkeletonPushoutBottom_app_ι_app, relativeSkeletonPushoutBottom_app_ι_app] at h'
  obtain ⟨e, ⟨he, hec⟩, -⟩ := existsUnique_iso_of_isNondegenerate Y f₁.down f₂.down _ _ hf₁
    (rep c₁.val).isNondegenerate hf₂ (rep c₂.val).isNondegenerate h'
  obtain rfl : c₁ = c₂ := Subtype.ext (by
    rw [← cellMk_rep c₁.val, ← cellMk_rep c₂.val]
    exact cellMk_eq_of_iso e hec)
  obtain rfl := hR _ _ c₁.property (rep c₁.val).isNondegenerate (rep c₁.val).not_mem e hec
  obtain rfl : f₁ = f₂ := ULift.ext _ _ (by simpa using he)
  rfl

theorem isPushout_relativeSkeleton_of_isDominant (R : Subfunctor Y) (n : ℕ)
    (hR : ∀ (a : A) (x : Y.obj (op a)), deg a = n → IsNondegenerate Y x →
      x ∉ R.obj (op a) → IsDominant x) :
    IsPushout (relativeSkeletonPushoutTop R n)
      (Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).ι)
      (Subfunctor.homOfLe (relativeSkeleton_monotone R n.le_succ))
      (relativeSkeletonPushoutBottom R n) :=
  IsPushout.of_forall_isPushout_app fun b ↦
    Types.isPushout_of_isPullback_of_mono'
      ((isPullback_relativeSkeleton R n).map ((evaluation _ _).obj b))
      (range_union_range_relativeSkeletonPushoutBottom R n b)
      (relativeSkeletonPushoutBottom_injective R n hR)

theorem isPushout_relativeSkeleton (R : Subfunctor Y) (hR : normalMonomorphisms A R.ι) (n : ℕ) :
    IsPushout (relativeSkeletonPushoutTop R n)
      (Limits.Sigma.map fun c : RelativeSkeletonCell R n ↦ (uliftBoundary.{w} (rep c.val).obj).ι)
      (Subfunctor.homOfLe (relativeSkeleton_monotone R n.le_succ))
      (relativeSkeletonPushoutBottom R n) :=
  isPushout_relativeSkeleton_of_isDominant R n fun _ _ _ hx hxR ↦
    (normalMonomorphisms_ι_iff R).1 hR _ hx hxR

end RelativeSkeleton

section Skeleton

theorem relativeSkeleton_bot_succ (n : ℕ) :
    relativeSkeleton (⊥ : Subfunctor Y) (n + 1) = skeletonSubfunctor n Y := by
  rw [relativeSkeleton_succ, bot_sup_eq]

theorem isPushout_skeleton_of_isDominant (n : ℕ)
    (hY : ∀ (a : A) (x : Y.obj (op a)), deg a = n → IsNondegenerate Y x → IsDominant x) :
    IsPushout (relativeSkeletonPushoutTop (⊥ : Subfunctor Y) n)
      (Limits.Sigma.map fun c : RelativeSkeletonCell (⊥ : Subfunctor Y) n ↦
        (uliftBoundary.{w} (rep c.val).obj).ι)
      (Subfunctor.homOfLe (relativeSkeleton_monotone (⊥ : Subfunctor Y) n.le_succ))
      (relativeSkeletonPushoutBottom (⊥ : Subfunctor Y) n) :=
  isPushout_relativeSkeleton_of_isDominant ⊥ n fun a x ha hx _ ↦ hY a x ha hx

theorem isPushout_skeleton [HasTrivialAutomorphisms A] (n : ℕ) :
    IsPushout (relativeSkeletonPushoutTop (⊥ : Subfunctor Y) n)
      (Limits.Sigma.map fun c : RelativeSkeletonCell (⊥ : Subfunctor Y) n ↦
        (uliftBoundary.{w} (rep c.val).obj).ι)
      (Subfunctor.homOfLe (relativeSkeleton_monotone (⊥ : Subfunctor Y) n.le_succ))
      (relativeSkeletonPushoutBottom (⊥ : Subfunctor Y) n) :=
  isPushout_skeleton_of_isDominant n fun _ x _ _ ↦ isDominant_of_hasTrivialAutomorphisms x

end Skeleton

end Atoms.Homotopical.EZCategory
