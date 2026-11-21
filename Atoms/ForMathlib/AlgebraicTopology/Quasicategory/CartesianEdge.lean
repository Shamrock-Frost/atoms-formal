import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.KanComplex
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.RightFibration
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace SSet

def IsCartesianEdge {X S : SSet.{u}} (p : X ⟶ S) (f : Δ[1] ⟶ X) : Prop :=
  modelCategoryQuillen.I.rlp (leibnizSlice (stdSimplex.δ 0) p f)

section Horn

private lemma boundary_join_sup_join_horn_one (n : ℕ) :
    (∂Δ[n]).join ⊤ ⊔ (⊤ : (Δ[n] : SSet.{u}).Subcomplex).join Λ[1, 1] =
      (Λ[n + 2, Fin.last (n + 2)]).preimage (stdSimplexJoinIso.{u} n 1).hom :=
  boundary_join_sup_join_horn n 0 1

lemma horn_one_one_ι :
    stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 0 = (horn.{u} 1 1).ι :=
  horn.hom_ext' fun j hj ↦ by
    obtain rfl : j = 0 := by
      fin_cases j
      · rfl
      · exact (hj rfl).elim
    rw [horn.ι_ι, ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext
      (horn.ι 1 0 hj ≫ stdSimplex.isTerminalObj₀.from _) (𝟙 _), Category.id_comp]

private noncomputable def hornInl (n : ℕ) :
    join Δ[n] Δ[0] ⟶ (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
  Subcomplex.lift (joinMap (𝟙 Δ[n]) (stdSimplex.δ 0) ≫ (stdSimplexJoinIso n 1).hom) (by
    rw [Subcomplex.range_comp, Subcomplex.image_le_iff, ← boundary_join_sup_join_horn_one]
    exact (range_joinMap_le (Subcomplex.topIso _).inv (horn.ι 1 0 (by decide))
      (Iso.inv_hom_id _) (horn.ι_ι _ _ _)).trans le_sup_right)

private noncomputable def hornInr (n : ℕ) :
    join (∂Δ[n] : SSet.{u}) Δ[1] ⟶ (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
  Subcomplex.lift (joinMap (∂Δ[n]).ι (𝟙 Δ[1]) ≫ (stdSimplexJoinIso n 1).hom) (by
    rw [Subcomplex.range_comp, Subcomplex.image_le_iff, ← boundary_join_sup_join_horn_one]
    exact (range_joinMap_le (𝟙 _) (Subcomplex.topIso _).inv (Category.id_comp _)
      (Iso.inv_hom_id _)).trans le_sup_left)

@[reassoc]
private lemma hornInl_ι (n : ℕ) :
    hornInl n ≫ Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplexJoinIso.{u} n 1).inv =
      joinMap (𝟙 Δ[n]) (stdSimplex.δ 0) := by
  rw [hornInl, Subcomplex.lift_ι_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
private lemma hornInr_ι (n : ℕ) :
    hornInr n ≫ Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplexJoinIso.{u} n 1).inv =
      joinMap (∂Δ[n]).ι (𝟙 Δ[1]) := by
  rw [hornInr, Subcomplex.lift_ι_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma isPushout_hornInl_hornInr (n : ℕ) :
    IsPushout (joinMap (∂Δ[n]).ι (𝟙 Δ[0])) (joinMap (𝟙 _) (stdSimplex.δ 0))
      (hornInl.{u} n) (hornInr n) :=
  IsPushout.of_forall_isPushout_app fun k ↦ by
    have m₁ : Mono ((joinMap (𝟙 Δ[n]) (stdSimplex.δ 0 : (Δ[0] : SSet.{u}) ⟶ Δ[1])).app k) :=
      (NatTrans.mono_iff_mono_app _).1 (mono_joinMap _ _) k
    have m₂ : Mono ((Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplexJoinIso.{u} n 1).inv).app k) :=
      (NatTrans.mono_iff_mono_app _).1 inferInstance k
    refine @Types.isPushout_of_isPullback_of_mono _ _ _ _ _ _ _ _ _
      ((Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplexJoinIso.{u} n 1).inv).app k) _ _
      ((isPullback_joinMap (∂Δ[n]).ι (stdSimplex.δ 0 : (Δ[0] : SSet.{u}) ⟶ Δ[1])).flip.app k)
      ((NatTrans.comp_app _ _ _).symm.trans (congr_app (hornInl_ι n) k))
      ((NatTrans.comp_app _ _ _).symm.trans (congr_app (hornInr_ι n) k)) m₁ m₂ ?_
      (fun x y _ _ h ↦ (mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app _).1 (mono_joinMap (∂Δ[n]).ι (𝟙 Δ[1])) k) h)
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : (stdSimplexJoinIso.{u} n 1).inv.app k x.1 ∈
        ((∂Δ[n]).join ⊤ ⊔ (⊤ : (Δ[n] : SSet.{u}).Subcomplex).join Λ[1, 1]).obj k := by
      rw [boundary_join_sup_join_horn_one, Subcomplex.preimage_obj, Set.mem_preimage,
        ← NatTrans.comp_app_apply, Iso.inv_hom_id]
      exact x.2
    have hinv (y) (hy : y = (stdSimplexJoinIso.{u} n 1).inv.app k x.1) :
        (stdSimplexJoinIso.{u} n 1).hom.app k y = x.1 := by
      rw [hy, ← NatTrans.comp_app_apply, Iso.inv_hom_id]
      rfl
    obtain hx | hx := hx
    · obtain ⟨y, hy⟩ := range_joinMap_le (𝟙 _) (Subcomplex.topIso _).hom (Category.id_comp _)
        (Category.comp_id _) _ hx
      exact Or.inr ⟨y, Subtype.ext (hinv _ hy)⟩
    · obtain ⟨y, hy⟩ := range_joinMap_le (Subcomplex.topIso _).hom
        (stdSimplex.isTerminalObj₀.from _) (Category.comp_id _) horn_one_one_ι.{u} _ hx
      exact Or.inl ⟨y, Subtype.ext (hinv _ hy)⟩

private noncomputable def hornPushoutObjObj (n : ℕ) :
    (Functor.curry.obj joinFunctor).PushoutObjObj (∂Δ[n]).ι
      (stdSimplex.δ 0 : (Δ[0] : SSet.{u}) ⟶ Δ[1]) where
  pt := Λ[n + 2, Fin.last (n + 2)]
  inl := hornInl n
  inr := hornInr n
  isPushout := isPushout_hornInl_hornInr n
  ι := Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplexJoinIso.{u} n 1).inv
  inl_ι := hornInl_ι n
  inr_ι := hornInr_ι n

private lemma yonedaEquiv_joinInclRight_comp_hornInr (n : ℕ) :
    yonedaEquiv (joinInclRight (∂Δ[n] : SSet.{u}) Δ[1] ≫ hornInr n) =
      horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp) := by
  apply Subtype.ext
  refine (yonedaEquiv_comp (joinInclRight (∂Δ[n] : SSet.{u}) Δ[1] ≫ hornInr n)
    Λ[n + 2, Fin.last (n + 2)].ι).symm.trans ?_
  rw [Category.assoc, hornInr, Subcomplex.lift_ι, joinInclRight_comp_joinMap_assoc,
    Category.id_comp, joinInclRight_comp_stdSimplexJoinIso_hom, yonedaEquiv_map]
  ext i
  fin_cases i
  · exact (congrArg Fin.val (AugmentedSimplexCategory.inr'_eval ⦋n⦌ ⦋1⦌ 0))
  · exact (congrArg Fin.val (AugmentedSimplexCategory.inr'_eval ⦋n⦌ ⦋1⦌ 1))

end Horn

theorem isCartesianEdge_iff_hasLift_horn {X S : SSet.{u}} (p : X ⟶ S) (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f ↔
      ∀ (n : ℕ) (a : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) (b : Δ[n + 2] ⟶ S)
        (sq : CommSq a Λ[n + 2, Fin.last (n + 2)].ι p b),
        a.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = yonedaEquiv f → sq.HasLift := by
  have hedge (n : ℕ) (a : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) :
      joinInclRight (∂Δ[n] : SSet.{u}) Δ[1] ≫ (hornPushoutObjObj n).inr ≫ a = f ↔
        a.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = yonedaEquiv f := by
    rw [← yonedaEquiv_joinInclRight_comp_hornInr, ← yonedaEquiv_comp, Equiv.apply_eq_iff_eq,
      Category.assoc]
    rfl
  let E (n : ℕ) := stdSimplexJoinIso.{u} n 1
  refine ⟨fun h n a b sq ha ↦ ?_, fun h _ _ _ ⟨n⟩ ↦ ?_⟩
  · have hsq : CommSq a (hornPushoutObjObj n).ι p ((E n).hom ≫ b) := ⟨by
      change a ≫ p = (Λ[n + 2, Fin.last (n + 2)].ι ≫ (E n).inv) ≫ (E n).hom ≫ b
      rw [Category.assoc, Iso.inv_hom_id_assoc, sq.w]⟩
    obtain ⟨l⟩ := ((hasLiftingProperty_leibnizSlice_iff (hornPushoutObjObj n) p f).1
      (h _ (modelCategoryQuillen.boundary_ι_mem_I n)) hsq ((hedge n a).2 ha)).exists_lift
    refine ⟨⟨⟨(E n).inv ≫ l.l, ?_, ?_⟩⟩⟩
    · exact (Category.assoc _ _ _).symm.trans l.fac_left
    · exact (Category.assoc _ _ _).trans ((congrArg _ l.fac_right).trans
        (Iso.inv_hom_id_assoc _ _))
  · refine (hasLiftingProperty_leibnizSlice_iff (hornPushoutObjObj n) p f).2 fun {u v} hsq hu ↦ ?_
    have sq' : CommSq u Λ[n + 2, Fin.last (n + 2)].ι p ((E n).inv ≫ v) := ⟨by
      rw [hsq.w]
      exact Category.assoc _ _ _⟩
    obtain ⟨l⟩ := (h n u _ sq' ((hedge n u).1 hu)).exists_lift
    refine ⟨⟨⟨(E n).hom ≫ l.l, ?_, ?_⟩⟩⟩
    · change (Λ[n + 2, Fin.last (n + 2)].ι ≫ (E n).inv) ≫ (E n).hom ≫ l.l = u
      rw [Category.assoc, Iso.inv_hom_id_assoc, l.fac_left]
    · exact (Category.assoc _ _ _).trans ((congrArg _ l.fac_right).trans
        (Iso.hom_inv_id_assoc _ _))

theorem isCartesianEdge_of_isIso {X S : SSet.{u}} (p : X ⟶ S) [IsIso p] (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f :=
  (isCartesianEdge_iff_hasLift_horn p f).2 fun _ _ _ sq _ ↦ HasLiftingProperty.sq_hasLift sq

theorem IsCartesianEdge.of_isPullback {X S X' S' : SSet.{u}} {p : X ⟶ S} {p' : X' ⟶ S'}
    {q : X' ⟶ X} {g : S' ⟶ S} (h : IsPullback q p' p g) {f : Δ[1] ⟶ X'}
    (hf : IsCartesianEdge p (f ≫ q)) : IsCartesianEdge p' f := by
  rw [isCartesianEdge_iff_hasLift_horn] at hf ⊢
  intro n a b sq ha
  obtain ⟨l⟩ := (hf n (a ≫ q) (b ≫ g) ⟨by rw [Category.assoc, h.w, ← Category.assoc, sq.w,
    Category.assoc]⟩ ((congrArg (q.app _) ha).trans (yonedaEquiv_comp f q).symm)).exists_lift
  refine ⟨⟨⟨h.lift l.l b l.fac_right, h.hom_ext ?_ ?_, h.lift_snd _ _ _⟩⟩⟩
  · rw [Category.assoc, h.lift_fst, l.fac_left]
  · rw [Category.assoc, h.lift_snd, sq.w]

theorem IsCartesianEdge.comp {X Y Z : SSet.{u}} {p : X ⟶ Y} {q : Y ⟶ Z} {f : Δ[1] ⟶ X}
    (hf : IsCartesianEdge p f) (hq : IsCartesianEdge q (f ≫ p)) : IsCartesianEdge (p ≫ q) f := by
  rw [isCartesianEdge_iff_hasLift_horn] at hf hq ⊢
  intro n a b sq ha
  obtain ⟨l₁⟩ := (hq n (a ≫ p) b ⟨(Category.assoc _ _ _).trans sq.w⟩
    ((congrArg (p.app _) ha).trans (yonedaEquiv_comp f p).symm)).exists_lift
  obtain ⟨l⟩ := (hf n a l₁.l ⟨l₁.fac_left.symm⟩ ha).exists_lift
  exact ⟨⟨⟨l.l, l.fac_left, by rw [← Category.assoc, l.fac_right, l₁.fac_right]⟩⟩⟩

theorem isCartesianEdge_iff_forall_pullback {X S : SSet.{u}} (p : X ⟶ S) (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f ↔ ∀ (n : ℕ) (b : Δ[n] ⟶ S) (f' : Δ[1] ⟶ pullback p b),
      f' ≫ pullback.fst p b = f → IsCartesianEdge (pullback.snd p b) f' := by
  refine ⟨fun hf n b f' hf' ↦ IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback p b)
    (by rwa [hf']), fun h ↦ (isCartesianEdge_iff_hasLift_horn p f).2 fun n a b sq ha ↦ ?_⟩
  let a' := pullback.lift a Λ[n + 2, Fin.last (n + 2)].ι sq.w
  let f' := yonedaEquiv.symm (a'.app _ (horn.edge (n + 2) (Fin.last (n + 2))
    (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp)))
  have hf' : f' ≫ pullback.fst p b = f := yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← NatTrans.comp_app_apply, pullback.lift_fst, ha])
  obtain ⟨l⟩ := ((isCartesianEdge_iff_hasLift_horn _ f').1 (h (n + 2) b f' hf') n a' (𝟙 _)
    ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩
    (Equiv.apply_symm_apply _ _).symm).exists_lift
  refine ⟨⟨⟨l.l ≫ pullback.fst p b, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, l.fac_left, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, l.fac_right, Category.id_comp]

section Simplices

private lemma horn_edge_last (n : ℕ) :
    horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
      (Fin.le_last _) (by simp) = (horn.ι (Fin.last (n + 2)) 0 (by simp)).app _
        (stdSimplex.edge.{u} (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _)) := by
  apply Subtype.ext
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    (congr_app (horn.ι_ι.{u} (Fin.last (n + 2)) 0 (by simp)) _) _).symm
  refine stdSimplex.ext _ _ fun i ↦ ?_
  fin_cases i <;> rfl

private lemma exists_simplex_of_isCartesianEdge {X S : SSet.{u}} {p : X ⟶ S} {f : Δ[1] ⟶ X}
    (hf : IsCartesianEdge p f) {n : ℕ}
    (s : ∀ j : Fin (n + 3), j ≠ Fin.last (n + 2) → X _⦋n + 1⦌)
    (hc : horn.IsCompatible (fun j hj ↦ yonedaEquiv.symm (s j hj)))
    (he : (yonedaEquiv.symm (s 0 (by simp))).app _ (stdSimplex.edge.{u} (n + 1)
      (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _)) = yonedaEquiv f)
    (τ : S _⦋n + 2⦌) (hτ : ∀ (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)),
      S.δ j τ = p.app _ (s j hj)) :
    ∃ σ : X _⦋n + 2⦌, (∀ (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)), X.δ j σ = s j hj) ∧
      p.app _ σ = τ := by
  have hsq : CommSq hc.desc Λ[n + 2, Fin.last (n + 2)].ι p (yonedaEquiv.symm τ) :=
    ⟨horn.hom_ext' fun j hj ↦ by
      rw [hc.ι_desc_assoc, horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, hτ j hj,
        ← yonedaEquiv_symm_comp]⟩
  obtain ⟨l⟩ := ((isCartesianEdge_iff_hasLift_horn p f).1 hf n _ _ hsq (by
    rw [horn_edge_last, ← he, ← NatTrans.comp_app_apply, hc.ι_desc])).exists_lift
  refine ⟨yonedaEquiv l.l, fun j hj ↦ ?_, ?_⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι _ j hj, Category.assoc, l.fac_left,
      hc.ι_desc, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, l.fac_right, Equiv.apply_symm_apply]

private lemma stdSimplex_edge_one :
    stdSimplex.edge.{u} (0 + 1) (Fin.last 0).castSucc (Fin.last (0 + 1)) (Fin.le_last _) =
      yonedaEquiv (𝟙 Δ[1]) :=
  stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl

private lemma stdSimplex_edge_two :
    stdSimplex.edge.{u} (1 + 1) (Fin.last 1).castSucc (Fin.last (1 + 1)) (Fin.le_last _) =
      yonedaEquiv (stdSimplex.δ 0) :=
  stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl

theorem exists_simplex_two_of_isCartesianEdge {X S : SSet.{u}} {p : X ⟶ S} {f : Δ[1] ⟶ X}
    (hf : IsCartesianEdge p f) (e : X _⦋1⦌) (he : X.δ 0 e = X.δ 0 (yonedaEquiv f))
    (τ : S _⦋2⦌) (h₀ : S.δ 0 τ = p.app _ (yonedaEquiv f)) (h₁ : S.δ 1 τ = p.app _ e) :
    ∃ σ : X _⦋2⦌, X.δ 0 σ = yonedaEquiv f ∧ X.δ 1 σ = e ∧ p.app _ σ = τ := by
  obtain ⟨σ, hσ, hpσ⟩ := exists_simplex_of_isCartesianEdge (n := 0) hf
    (fun j _ ↦ ![yonedaEquiv f, e, e] j) (fun j k hj hk hjk ↦ by
      fin_cases j <;> fin_cases k
      all_goals try exact absurd hjk (by decide)
      all_goals try exact (hk rfl).elim
      simp only [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg _ he.symm)
    (by rw [stdSimplex_edge_one, ← yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]; rfl)
    τ (fun j hj ↦ by
      fin_cases j
      · exact h₀
      · exact h₁
      · exact (hj rfl).elim)
  exact ⟨σ, hσ 0 (by decide), hσ 1 (by decide), hpσ⟩

private lemma exists_simplex_three_of_isCartesianEdge {X S : SSet.{u}} {p : X ⟶ S}
    {f : Δ[1] ⟶ X} (hf : IsCartesianEdge p f) (s₀ s₁ s₂ : X _⦋2⦌)
    (h₀₁ : X.δ 0 s₀ = X.δ 0 s₁) (h₀₂ : X.δ 1 s₀ = X.δ 0 s₂) (h₁₂ : X.δ 1 s₁ = X.δ 1 s₂)
    (he : X.δ 0 s₀ = yonedaEquiv f) (τ : S _⦋3⦌) (hτ₀ : S.δ 0 τ = p.app _ s₀)
    (hτ₁ : S.δ 1 τ = p.app _ s₁) (hτ₂ : S.δ 2 τ = p.app _ s₂) :
    ∃ σ : X _⦋3⦌, X.δ 0 σ = s₀ ∧ X.δ 1 σ = s₁ ∧ X.δ 2 σ = s₂ ∧ p.app _ σ = τ := by
  obtain ⟨σ, hσ, hpσ⟩ := exists_simplex_of_isCartesianEdge (n := 1) hf
    (fun j _ ↦ ![s₀, s₁, s₂, s₀] j) (fun j k hj hk hjk ↦ by
      fin_cases j <;> fin_cases k
      all_goals try exact absurd hjk (by decide)
      all_goals try exact (hk rfl).elim
      all_goals simp only [stdSimplex.δ_comp_yonedaEquiv_symm]
      · exact congrArg _ h₀₁
      · exact congrArg _ h₀₂
      · exact congrArg _ h₁₂)
    (by rw [stdSimplex_edge_two, ← yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm,
      Equiv.apply_symm_apply]; exact he)
    τ (fun j hj ↦ by
      fin_cases j
      · exact hτ₀
      · exact hτ₁
      · exact hτ₂
      · exact (hj rfl).elim)
  exact ⟨σ, hσ 0 (by decide), hσ 1 (by decide), hσ 2 (by decide), hpσ⟩

end Simplices

theorem isCartesianEdge_of_invStruct {C D : SSet.{u}} (p : C ⟶ D) [InnerFibration p]
    [C.Quasicategory] [D.Quasicategory] {f : Δ[1] ⟶ C}
    (hf : Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct) : IsCartesianEdge p f :=
  (isCartesianEdge_iff_hasLift_horn p f).2 fun _ _ _ sq ha ↦
    hasLift_horn_last_of_invStruct p sq (by rw [ha]; exact hf)

private lemma nonempty_invStruct_of_isCartesianEdge {X T : SSet.{u}} (hT : IsTerminal T)
    {f : Δ[1] ⟶ X} (hf : IsCartesianEdge (hT.from X) f) :
    Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct := by
  have hT' (k : ℕ) (a b : T _⦋k⦌) : a = b :=
    yonedaEquiv.symm.injective (hT.hom_ext _ _)
  set e := yonedaEquiv f
  obtain ⟨σ₁, h₀, h₁, -⟩ := exists_simplex_two_of_isCartesianEdge hf (X.σ 0 (X.δ 0 e))
    (δ_comp_σ_self_apply (S := X) (n := 0) 0 _) ((hT.from X).app _ (X.σ 0 e)) (hT' _ _ _)
    (hT' _ _ _)
  let g : Edge (X.δ 0 e) (X.δ 1 e) := Edge.mk (X.δ 2 σ₁)
    ((δ_comp_δ_self_apply (i := 1) σ₁).symm.trans
      ((congrArg _ h₁).trans (δ_comp_σ_succ_apply (S := X) 0 _)))
    ((δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ₁).trans (congrArg _ h₀))
  obtain ⟨σ, hσ₀, hσ₁, hσ₂, -⟩ := exists_simplex_three_of_isCartesianEdge hf σ₁ (X.σ 0 e)
    (X.σ 1 e) (h₀.trans (δ_comp_σ_self_apply (S := X) 0 e).symm)
    (h₁.trans (δ_comp_σ_of_le_apply (S := X) (n := 0) (i := 0) (j := 0) (by decide) e).symm)
    ((δ_comp_σ_succ_apply (S := X) 0 e).trans (δ_comp_σ_self_apply (S := X) 1 e).symm) h₀
    ((hT.from X).app _ (X.σ 0 σ₁)) (hT' _ _ _) (hT' _ _ _) (hT' _ _ _)
  refine ⟨{ inv := g
            homInvId := Edge.CompStruct.mk (X.δ 3 σ) ?_ ?_ ?_
            invHomId := Edge.CompStruct.mk σ₁ rfl h₀ h₁ }⟩
  · exact (δ_comp_δ_self_apply (i := 2) σ).symm.trans
      ((congrArg _ hσ₂).trans (δ_comp_σ_succ_apply (S := X) 1 e))
  · exact (δ_comp_δ_apply (i := 0) (j := 2) (by decide) σ).trans (congrArg _ hσ₀)
  · exact (δ_comp_δ_apply (i := 1) (j := 2) (by decide) σ).trans ((congrArg _ hσ₁).trans
      (δ_comp_σ_of_gt_apply (S := X) (n := 0) (i := 1) (j := 0) (by decide) e))

theorem isCartesianEdge_iff_invStruct_of_isTerminal {X T : SSet.{u}} [X.Quasicategory]
    (hT : IsTerminal T) (f : Δ[1] ⟶ X) :
    IsCartesianEdge (hT.from X) f ↔ Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct := by
  have : T.Quasicategory :=
    (quasicategory_iff_of_isTerminal (𝟙 T) hT).2 ⟨innerFibrations.id_mem T⟩
  have : InnerFibration (hT.from X) := (quasicategory_iff_of_isTerminal _ hT).1 inferInstance
  exact ⟨nonempty_invStruct_of_isCartesianEdge hT, isCartesianEdge_of_invStruct _⟩

theorem invStruct_iff_isCartesianEdge {C D : SSet.{u}} [C.Quasicategory] [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (f : Δ[1] ⟶ C) :
    Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct ↔
      IsCartesianEdge p f ∧ Nonempty (Edge.mk' (yonedaEquiv (f ≫ p))).InvStruct := by
  refine ⟨fun hf ↦ ⟨isCartesianEdge_of_invStruct p hf, ⟨(hf.some.map p).ofEq ?_⟩⟩,
    fun ⟨hf, hfp⟩ ↦ ?_⟩
  · rw [Edge.map_edge, Edge.mk'_edge, Edge.mk'_edge, yonedaEquiv_comp]
  · have hq := (isCartesianEdge_iff_invStruct_of_isTerminal terminalIsTerminal (f ≫ p)).2 hfp
    have hpq := hf.comp hq
    rw [Subsingleton.elim (p ≫ terminalIsTerminal.from D) (terminalIsTerminal.from C)] at hpq
    exact (isCartesianEdge_iff_invStruct_of_isTerminal terminalIsTerminal f).1 hpq

theorem isCartesianEdge_id {C D : SSet.{u}} [C.Quasicategory] [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (x : C _⦋0⦌) :
    IsCartesianEdge p (yonedaEquiv.symm (Edge.id x).edge) :=
  ((invStruct_iff_isCartesianEdge p _).1
    ⟨(Edge.InvStruct.invStructId x).ofEq (by rw [Edge.mk'_edge, Equiv.apply_symm_apply])⟩).1

section TrivialFibration

private lemma trivialFibration_of_rightFibrations_of_comp {A B C : SSet.{u}} {g : A ⟶ B}
    {h : B ⟶ C} (hg : rightFibrations g) (hh : modelCategoryQuillen.I.rlp h)
    (hgh : modelCategoryQuillen.I.rlp (g ≫ h)) : modelCategoryQuillen.I.rlp g := by
  rintro _ _ _ ⟨m⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨l₀⟩ := ((hgh _ ⟨m⟩).sq_hasLift (⟨by rw [← Category.assoc, sq.w, Category.assoc]⟩ :
    CommSq a (∂Δ[m]).ι (g ≫ h) (b ≫ h))).exists_lift
  have hσ : (∂Δ[m]).ι ≫ l₀.l ≫ g = a ≫ g := by rw [← Category.assoc, l₀.fac_left]
  let sq₁ := Subcomplex.unionProd.pushoutObjObj (∂Δ[m]) (∂Δ[1])
  have hu₁ : (∂Δ[m]).ι ▷ _ ≫ boundaryOneDesc b (l₀.l ≫ g) = _ ◁ (∂Δ[1]).ι ≫ fst _ _ ≫ a ≫ g := by
    rw [whiskerRight_boundaryOneDesc, hσ, ← sq.w, boundaryOneDesc_self, whiskerLeft_fst_assoc]
  let u₁ := sq₁.isPushout.desc (boundaryOneDesc b (l₀.l ≫ g)) (fst _ _ ≫ a ≫ g) hu₁
  have w₁ : u₁ ≫ h = sq₁.ι ≫ fst _ _ ≫ b ≫ h := by
    refine sq₁.isPushout.hom_ext ?_ ?_
    · rw [sq₁.isPushout.inl_desc_assoc, sq₁.inl_ι_assoc, boundaryOneDesc_comp, Category.assoc,
        l₀.fac_right, boundaryOneDesc_self]
      exact (whiskerLeft_fst_assoc _ _ _).symm
    · rw [sq₁.isPushout.inr_desc_assoc, sq₁.inr_ι_assoc, sq.w]
      simp only [Category.assoc]
      exact (whiskerRight_fst_assoc _ _ _).symm
  have : Mono sq₁.ι := by
    rw [Subcomplex.unionProd.pushoutObjObj_ι]
    exact Subcomplex.instMonoι _
  have hmono : modelCategoryQuillen.I.rlp.llp sq₁.ι := by
    rw [← rlp_monomorphisms]
    exact le_llp_rlp _ _ (monomorphisms.infer_property _)
  obtain ⟨H⟩ := ((hmono _ hh).sq_hasLift (⟨w₁⟩ : CommSq u₁ sq₁.ι h (fst _ _ ≫ b ≫ h))).exists_lift
  have hH := ι_comp_of_boundaryOneDesc (H := H.l) (f₀ := b) (f₁ := l₀.l ≫ g)
    ((sq₁.inl_ι_assoc H.l).symm.trans ((congrArg (sq₁.inl ≫ ·) H.fac_left).trans
      (sq₁.isPushout.inl_desc _ _ _)))
  have hHr : (∂Δ[m]).ι ▷ Δ[1] ≫ H.l = fst _ _ ≫ a ≫ g :=
    (sq₁.inr_ι_assoc H.l).symm.trans ((congrArg (sq₁.inr ≫ ·) H.fac_left).trans
      (sq₁.isPushout.inr_desc _ _ _))
  let sq₂ := Subcomplex.unionProd.pushoutObjObj (∂Δ[m]) Λ[1, 1]
  have hu₂ : (∂Δ[m]).ι ▷ _ ≫ fst _ _ ≫ l₀.l = _ ◁ Λ[1, 1].ι ≫ fst _ _ ≫ a := by
    rw [whiskerRight_fst_assoc, l₀.fac_left, whiskerLeft_fst_assoc]
  let u₂ := sq₂.isPushout.desc (fst _ _ ≫ l₀.l) (fst _ _ ≫ a) hu₂
  have w₂ : u₂ ≫ g = sq₂.ι ≫ H.l := by
    refine sq₂.isPushout.hom_ext ?_ ?_
    · rw [sq₂.isPushout.inl_desc_assoc, sq₂.inl_ι_assoc]
      exact (Category.assoc _ _ _).trans (whiskerLeft_horn_comp hH.2).symm
    · rw [sq₂.isPushout.inr_desc_assoc, sq₂.inr_ι_assoc]
      exact (Category.assoc _ _ _).trans hHr.symm
  have hsq := rightAnodyneExtensions_pushoutObjObjι sq₂
    (rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1)) g hg
  obtain ⟨K⟩ := (hsq.sq_hasLift (⟨w₂⟩ : CommSq u₂ sq₂.ι g H.l)).exists_lift
  refine ⟨⟨⟨ι₀ ≫ K.l, ?_, ?_⟩⟩⟩
  · rw [← ι₀_comp_assoc]
    exact (congrArg (ι₀ ≫ ·) ((sq₂.inr_ι_assoc K.l).symm.trans ((congrArg (sq₂.inr ≫ ·)
      K.fac_left).trans (sq₂.isPushout.inr_desc _ _ _)))).trans
        (by rw [ι₀_fst_assoc])
  · rw [Category.assoc, K.fac_right, hH.1]

end TrivialFibration

section Comp

variable {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) (f : Δ[1] ⟶ X)

private noncomputable def cartesianTargetMap :
    pullback ((slice Δ[0]).map (Under.homMk p (by simp) :
        Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)))
      (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p))) ⟶
    pullback ((slice Δ[0]).map (Under.homMk (p ≫ q) (by simp) :
        Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p ≫ q)))
      (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p ≫ q))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (slice Δ[1]).map
    (Under.homMk q (by simp) : Under.mk (f ≫ p) ⟶ Under.mk (f ≫ p ≫ q))) (by
      rw [Category.assoc, ← sliceRes_naturality, ← pullback.condition_assoc, ← Functor.map_comp]
      rfl)

private lemma leibnizSlice_comp_cartesianTargetMap :
    leibnizSlice (stdSimplex.δ 0) p f ≫ cartesianTargetMap p q f =
      leibnizSlice (stdSimplex.δ 0) (p ≫ q) f := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, cartesianTargetMap, pullback.lift_fst, leibnizSlice_fst, leibnizSlice_fst]
  · rw [Category.assoc, cartesianTargetMap, pullback.lift_snd, leibnizSlice_snd_assoc,
      leibnizSlice_snd, ← Functor.map_comp]
    rfl

private lemma trivialFibration_cartesianTargetMap (hq : IsCartesianEdge q (f ≫ p)) :
    modelCategoryQuillen.I.rlp (cartesianTargetMap p q f) := by
  rintro _ _ _ ⟨m⟩
  refine ⟨fun {α β} sq ↦ ?_⟩
  let φ := (slice Δ[1]).map (Under.homMk (𝟙 Z) (by simp) :
    Under.mk (f ≫ p ≫ q) ⟶ Under.mk ((f ≫ p) ≫ q))
  let ψ := (slice Δ[1]).map (Under.homMk (𝟙 Z) (by simp) :
    Under.mk ((f ≫ p) ≫ q) ⟶ Under.mk (f ≫ p ≫ q))
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    rw [← Functor.map_comp, ← (slice Δ[1]).map_id]
    congr 1
  have hk₁ : cartesianTargetMap p q f ≫ pullback.fst _ _ = pullback.fst _ _ :=
    pullback.lift_fst _ _ _
  have hk₂ : cartesianTargetMap p q f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (slice Δ[1]).map
      (Under.homMk q (by simp) : Under.mk (f ≫ p) ⟶ Under.mk (f ≫ p ≫ q)) :=
    pullback.lift_snd _ _ _
  have hqφ : (slice Δ[1]).map (Under.homMk q (by simp) : Under.mk (f ≫ p) ⟶ Under.mk (f ≫ p ≫ q))
      ≫ φ = (slice Δ[1]).map (Under.homMk q : Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ p) ≫ q)) := by
    rw [← Functor.map_comp]
    congr 1
  obtain ⟨β', hβ'₁, hβ'₂⟩ : ∃ β' : Δ[m] ⟶ pullback ((slice Δ[0]).map (Under.homMk q (by simp) :
      Under.mk (stdSimplex.δ 0 ≫ f ≫ p) ⟶ Under.mk (stdSimplex.δ 0 ≫ (f ≫ p) ≫ q)))
      (sliceRes (stdSimplex.δ 0) (Under.mk ((f ≫ p) ≫ q))),
      β' ≫ pullback.fst _ _ = β ≫ pullback.fst _ _ ≫ (slice Δ[0]).map (Under.homMk p (by simp) :
        Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)) ∧
      β' ≫ pullback.snd _ _ = β ≫ pullback.snd _ _ ≫ φ := by
    refine ⟨pullback.lift _ _ ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hφ := sliceRes_naturality (stdSimplex.δ 0)
      (Under.homMk (𝟙 Z) (by simp) : Under.mk (f ≫ p ≫ q) ⟶ Under.mk ((f ≫ p) ≫ q))
    simp only [Category.assoc, φ]
    rw [← hφ, ← pullback.condition_assoc, ← Functor.map_comp, ← Functor.map_comp]
    congr 3
  have hsq : CommSq (α ≫ pullback.snd _ _) (∂Δ[m]).ι
      (leibnizSlice (stdSimplex.δ 0) q (f ≫ p)) β' :=
    ⟨pullback.hom_ext (by
      simp only [Category.assoc, leibnizSlice_fst, hβ'₁, ← pullback.condition, ← sq.w_assoc,
        reassoc_of% hk₁]) (by
      simp only [Category.assoc, leibnizSlice_snd, hβ'₂, ← sq.w_assoc, reassoc_of% hk₂, hqφ])⟩
  obtain ⟨l⟩ := ((hq _ ⟨m⟩).sq_hasLift hsq).exists_lift
  have hl₁ : l.l ≫ sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p)) = β ≫ pullback.fst _ _ ≫
      (slice Δ[0]).map (Under.homMk p (by simp) :
        Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)) := by
    have h := l.fac_right =≫ pullback.fst _ _
    simp only [Category.assoc, leibnizSlice_fst, hβ'₁] at h
    exact h
  have hl₂ : l.l ≫ (slice Δ[1]).map (Under.homMk q : Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ p) ≫ q)) =
      β ≫ pullback.snd _ _ ≫ φ := by
    have h := l.fac_right =≫ pullback.snd _ _
    simp only [Category.assoc, leibnizSlice_snd, hβ'₂] at h
    exact h
  obtain ⟨L, hL₁, hL₂⟩ : ∃ L : Δ[m] ⟶ pullback ((slice Δ[0]).map (Under.homMk p (by simp) :
      Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)))
      (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p))),
      L ≫ pullback.fst _ _ = β ≫ pullback.fst _ _ ∧ L ≫ pullback.snd _ _ = l.l :=
    ⟨pullback.lift _ _ hl₁.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [← hqφ] at hl₂
  have hl₃ := hl₂ =≫ ψ
  simp only [Category.assoc, hφψ, Category.comp_id] at hl₃
  refine ⟨⟨⟨L, pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩⟩⟩
  · simp only [Category.assoc, hL₁, ← sq.w_assoc, hk₁]
  · simp only [Category.assoc, hL₂, l.fac_left]
  · simp only [Category.assoc, hk₁, hL₁]
  · simp only [Category.assoc, hk₂, reassoc_of% hL₂, hl₃]

end Comp

theorem IsCartesianEdge.comp_iff {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) [InnerFibration p]
    {f : Δ[1] ⟶ X} (hq : IsCartesianEdge q (f ≫ p)) :
    IsCartesianEdge p f ↔ IsCartesianEdge (p ≫ q) f :=
  ⟨fun hf ↦ hf.comp hq, fun h ↦ trivialFibration_of_rightFibrations_of_comp
    (rightFibrations_leibnizSlice _ p f) (trivialFibration_cartesianTargetMap p q f hq)
    (by rw [leibnizSlice_comp_cartesianTargetMap]; exact h)⟩

section RightCancellation

variable {C D : SSet.{u}} (p : C ⟶ D)

private lemma isPullback_of_eq {P X Y Z : SSet.{u}} {fst fst' : P ⟶ X} {snd snd' : P ⟶ Y}
    {f f' : X ⟶ Z} {g g' : Y ⟶ Z} (h : IsPullback fst snd f g) (h₁ : fst = fst')
    (h₂ : snd = snd') (h₃ : f = f') (h₄ : g = g') : IsPullback fst' snd' f' g' := by
  subst h₁ h₂ h₃ h₄
  exact h

private noncomputable def leibnizSliceRes {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T) (e : T ⟶ C) :
    pullback ((slice B).map (Under.homMk p (by simp) : Under.mk (b ≫ e) ⟶ Under.mk (b ≫ e ≫ p)))
      (sliceRes b (Under.mk (e ≫ p))) ⟶
    pullback ((slice A).map (Under.homMk p (by simp) :
      Under.mk ((a ≫ b) ≫ e) ⟶ Under.mk ((a ≫ b) ≫ e ≫ p)))
      (sliceRes (a ≫ b) (Under.mk (e ≫ p))) :=
  pullback.lift (pullback.fst _ _ ≫ sliceRes a (Under.mk (b ≫ e))) (pullback.snd _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (sliceRes_naturality a
      (Under.homMk p (by simp) : Under.mk (b ≫ e) ⟶ Under.mk (b ≫ e ≫ p)))).trans
      ((pullback.condition_assoc _).trans (congrArg (_ ≫ ·) (sliceRes_comp a b _)))))

private lemma leibnizSlice_comp_leibnizSliceRes {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T)
    (e : T ⟶ C) : leibnizSlice b p e ≫ leibnizSliceRes p a b e = leibnizSlice (a ≫ b) p e := by
  refine pullback.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
    exact (leibnizSlice_fst_assoc _ _ _ _).trans ((sliceRes_comp a b (Under.mk e)).trans
      (leibnizSlice_fst _ _ _).symm)
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
    exact (leibnizSlice_snd _ _ _).trans (leibnizSlice_snd _ _ _).symm

private noncomputable def leibnizSliceBaseRes {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T)
    (e : T ⟶ C) :
    pullback ((slice A).map (Under.homMk p (by simp) :
      Under.mk ((a ≫ b) ≫ e) ⟶ Under.mk ((a ≫ b) ≫ e ≫ p)))
      (sliceRes (a ≫ b) (Under.mk (e ≫ p))) ⟶
    pullback ((slice A).map (Under.homMk p (by simp) :
      Under.mk (a ≫ b ≫ e) ⟶ Under.mk (a ≫ (b ≫ e) ≫ p)))
      (sliceRes a (Under.mk ((b ≫ e) ≫ p))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ sliceRes b (Under.mk (e ≫ p)))
    (pullback.condition.trans ((congrArg (_ ≫ ·) (sliceRes_comp a b _).symm).trans
      (Category.assoc _ _ _).symm))

private lemma isPullback_leibnizSliceBaseRes {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T)
    (e : T ⟶ C) :
    IsPullback (pullback.snd _ _) (leibnizSliceBaseRes p a b e) (sliceRes b (Under.mk (e ≫ p)))
      (pullback.snd _ _) := by
  have h₁ : leibnizSliceBaseRes p a b e ≫ pullback.fst _ _ = pullback.fst _ _ :=
    pullback.lift_fst _ _ _
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback _ _).flip
  exact isPullback_of_eq (IsPullback.of_hasPullback _ _).flip rfl h₁.symm
    (sliceRes_comp a b _).symm rfl

private lemma isPullback_leibnizSliceRes {A B T : SSet.{u}} (a : A ⟶ B) (b : B ⟶ T) (e : T ⟶ C) :
    IsPullback (pullback.fst _ _) (leibnizSliceRes p a b e) (leibnizSlice a p (b ≫ e))
      (leibnizSliceBaseRes p a b e) := by
  have h₁ : leibnizSliceRes p a b e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ ?_ (isPullback_leibnizSliceBaseRes p a b e).flip
  · exact isPullback_of_eq (IsPullback.of_hasPullback _ _) rfl h₁.symm
      (leibnizSlice_snd _ _ _).symm rfl
  · refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (leibnizSlice_fst _ _ _)).trans
        ((pullback.lift_fst _ _ _).symm.trans ((congrArg (_ ≫ ·)
          (pullback.lift_fst _ _ _)).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (leibnizSlice_snd _ _ _)).trans
        (pullback.condition.trans ((congrArg (· ≫ _) h₁.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).symm.trans (Category.assoc _ _ _).symm)))))

private lemma exists_lift_of_trivialFibration {X Y K : SSet.{u}} {t : X ⟶ Y}
    (ht : modelCategoryQuillen.I.rlp t) (v : K ⟶ Y) : ∃ v' : K ⟶ X, v' ≫ t = v := by
  have hm : modelCategoryQuillen.I.rlp.llp (⊥ : K.Subcomplex).ι := by
    rw [← rlp_monomorphisms]
    exact le_llp_rlp _ _ (monomorphisms.infer_property _)
  obtain ⟨l⟩ := ((hm _ ht).sq_hasLift (⟨Subcomplex.isInitialBot.hom_ext _ _⟩ :
    CommSq (Subcomplex.isInitialBot.to X) (⊥ : K.Subcomplex).ι t v)).exists_lift
  exact ⟨l.l, l.fac_right⟩

private lemma trivialFibration_of_comp {X Y Z : SSet.{u}} {b : X ⟶ Y} {a : Y ⟶ Z}
    (hb : modelCategoryQuillen.I.rlp b) (hba : modelCategoryQuillen.I.rlp (b ≫ a)) :
    modelCategoryQuillen.I.rlp a := by
  rintro _ _ _ ⟨m⟩
  refine ⟨fun {u v} sq ↦ ?_⟩
  obtain ⟨u', hu'⟩ := exists_lift_of_trivialFibration hb u
  obtain ⟨l⟩ := ((hba _ ⟨m⟩).sq_hasLift (⟨by rw [← Category.assoc, hu', sq.w]⟩ :
    CommSq u' (∂Δ[m]).ι (b ≫ a) v)).exists_lift
  exact ⟨⟨⟨l.l ≫ b, by rw [← Category.assoc, l.fac_left, hu'],
    by rw [Category.assoc, l.fac_right]⟩⟩⟩

private lemma trivialFibration_of_isPullback {Y' Y Q P : SSet.{u}} {f : Y' ⟶ Y} {r' : Y' ⟶ Q}
    {r : Y ⟶ P} {t : Q ⟶ P} (h : IsPullback f r' r t) (hr' : modelCategoryQuillen.I.rlp r')
    (ht : modelCategoryQuillen.I.rlp t) : modelCategoryQuillen.I.rlp r := by
  rintro _ _ _ ⟨m⟩
  refine ⟨fun {u v} sq ↦ ?_⟩
  obtain ⟨q₀, hq₀⟩ := exists_lift_of_trivialFibration ht ((∂Δ[m]).ι ≫ v)
  obtain ⟨q⟩ := ((ht _ ⟨m⟩).sq_hasLift (⟨hq₀⟩ : CommSq q₀ (∂Δ[m]).ι t v)).exists_lift
  obtain ⟨l⟩ := ((hr' _ ⟨m⟩).sq_hasLift (⟨(h.lift_snd _ _ _).trans q.fac_left.symm⟩ :
    CommSq (h.lift u q₀ (sq.w.trans hq₀.symm)) (∂Δ[m]).ι r' q.l)).exists_lift
  refine ⟨⟨⟨l.l ≫ f, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, l.fac_left, h.lift_fst]
  · rw [Category.assoc, h.w, ← Category.assoc, l.fac_right, q.fac_right]

variable [InnerFibration p]

private lemma trivialFibration_leibnizSlice_comp_iff [D.Quasicategory] {A B T : SSet.{u}}
    (a : A ⟶ B) {b : B ⟶ T} (hb : leftAnodyneExtensions b) (e : T ⟶ C) :
    modelCategoryQuillen.I.rlp (leibnizSlice a p (b ≫ e)) ↔
      modelCategoryQuillen.I.rlp (leibnizSlice (a ≫ b) p e) := by
  have hψ : modelCategoryQuillen.I.rlp (leibnizSliceBaseRes p a b e) :=
    modelCategoryQuillen.I.rlp.of_isPullback (isPullback_leibnizSliceBaseRes p a b e)
      (trivialFibration_sliceRes hb _)
  rw [← leibnizSlice_comp_leibnizSliceRes]
  refine ⟨fun h ↦ modelCategoryQuillen.I.rlp.comp_mem _ _ (trivialFibration_leibnizSlice hb p e)
    (modelCategoryQuillen.I.rlp.of_isPullback (isPullback_leibnizSliceRes p a b e) h),
    fun h ↦ trivialFibration_of_isPullback (isPullback_leibnizSliceRes p a b e)
      (trivialFibration_of_comp (trivialFibration_leibnizSlice hb p e) h) hψ⟩

private lemma trivialFibration_leibnizSlice_iff_comp {A B T : SSet.{u}} {a : A ⟶ B} (b : B ⟶ T)
    [Mono b] (e : T ⟶ C) (ha : modelCategoryQuillen.I.rlp (leibnizSlice a p (b ≫ e))) :
    modelCategoryQuillen.I.rlp (leibnizSlice b p e) ↔
      modelCategoryQuillen.I.rlp (leibnizSlice (a ≫ b) p e) := by
  have hres := modelCategoryQuillen.I.rlp.of_isPullback (isPullback_leibnizSliceRes p a b e) ha
  rw [← leibnizSlice_comp_leibnizSliceRes]
  exact ⟨fun h ↦ modelCategoryQuillen.I.rlp.comp_mem _ _ h hres,
    fun h ↦ trivialFibration_of_rightFibrations_of_comp (rightFibrations_leibnizSlice b p e) hres h⟩

end RightCancellation

theorem isCartesianEdge_δ_two_iff_δ_one {C D : SSet.{u}} [D.Quasicategory]
    (p : C ⟶ D) [InnerFibration p] (σ : Δ[2] ⟶ C)
    (hg : IsCartesianEdge p (stdSimplex.δ 0 ≫ σ)) :
    IsCartesianEdge p (stdSimplex.δ 2 ≫ σ) ↔ IsCartesianEdge p (stdSimplex.δ 1 ≫ σ) := by
  have h₁ : (stdSimplex.δ 0 ≫ stdSimplex.δ 2 : Δ[0] ⟶ Δ[2]) = stdSimplex.δ 1 ≫ stdSimplex.δ 0 :=
    stdSimplex.δ_comp_δ (n := 0) (i := 0) (j := 1) (by decide)
  have h₂ : (stdSimplex.δ 0 ≫ stdSimplex.δ 1 : Δ[0] ⟶ Δ[2]) = stdSimplex.δ 0 ≫ stdSimplex.δ 0 :=
    stdSimplex.δ_comp_δ (n := 0) (i := 0) (j := 0) (by decide)
  rw [IsCartesianEdge, IsCartesianEdge,
    trivialFibration_leibnizSlice_comp_iff p _ (leftAnodyneExtensions_stdSimplex_δ_of_ne_zero
      (i := 2) (by decide)),
    trivialFibration_leibnizSlice_comp_iff p _ (leftAnodyneExtensions_stdSimplex_δ_of_ne_zero
      (i := 1) (by decide)),
    h₁, h₂,
    ← trivialFibration_leibnizSlice_iff_comp p _ σ
      (trivialFibration_leibnizSlice leftAnodyneExtensions_stdSimplex_δ_one p _),
    ← trivialFibration_leibnizSlice_iff_comp p _ σ hg]

end SSet
