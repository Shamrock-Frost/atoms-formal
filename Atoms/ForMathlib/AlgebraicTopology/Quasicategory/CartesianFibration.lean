import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianEdge

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

def IsLocallyCartesianEdge {X S : SSet.{u}} (p : X ⟶ S) (e : Δ[1] ⟶ X) : Prop :=
  IsCartesianEdge (pullback.snd p (e ≫ p)) (pullback.lift e (𝟙 Δ[1]) (Category.id_comp _).symm)

theorem IsCartesianEdge.isLocallyCartesianEdge {X S : SSet.{u}} {p : X ⟶ S} {e : Δ[1] ⟶ X}
    (he : IsCartesianEdge p e) : IsLocallyCartesianEdge p e :=
  IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback _ _) (by rwa [pullback.lift_fst])

section Locality

variable {X S : SSet.{u}} (p : X ⟶ S)

instance quasicategory_stdSimplex (n : ℕ) : (Δ[n] : SSet.{u}).Quasicategory :=
  have : InnerFibration (stdSimplex.isoNerve.{u} n).hom := ⟨innerFibrations.of_isIso _⟩
  quasicategory_of_innerFibration (stdSimplex.isoNerve.{u} n).hom

instance innerFibration_pullback_snd [InnerFibration p] {K : SSet.{u}} (b : K ⟶ S) :
    InnerFibration (pullback.snd p b) :=
  ⟨innerFibrations.of_isPullback (IsPullback.of_hasPullback p b) (mem_innerFibrations p)⟩

noncomputable def pullbackMap {K K' : SSet.{u}} (b : K ⟶ S) (g : K' ⟶ K) (c : K' ⟶ S)
    (hc : g ≫ b = c) : pullback p c ⟶ pullback p b :=
  pullback.lift (pullback.fst p c) (pullback.snd p c ≫ g) (by
    rw [pullback.condition, Category.assoc, hc])

@[reassoc (attr := simp)]
lemma pullbackMap_fst {K K' : SSet.{u}} (b : K ⟶ S) (g : K' ⟶ K) (c : K' ⟶ S)
    (hc : g ≫ b = c) : pullbackMap p b g c hc ≫ pullback.fst p b = pullback.fst p c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackMap_snd {K K' : SSet.{u}} (b : K ⟶ S) (g : K' ⟶ K) (c : K' ⟶ S)
    (hc : g ≫ b = c) : pullbackMap p b g c hc ≫ pullback.snd p b = pullback.snd p c ≫ g :=
  pullback.lift_snd _ _ _

lemma isPullback_pullbackMap {K K' : SSet.{u}} (b : K ⟶ S) (g : K' ⟶ K) (c : K' ⟶ S)
    (hc : g ≫ b = c) :
    IsPullback (pullbackMap p b g c hc) (pullback.snd p c) (pullback.snd p b) g :=
  IsPullback.of_right (by rw [pullbackMap_fst, hc]; exact IsPullback.of_hasPullback p c)
    (pullbackMap_snd _ _ _ _ _) (IsPullback.of_hasPullback p b)

lemma isLocallyCartesianEdge_of_pullback {K : SSet.{u}} (b : K ⟶ S)
    {f : Δ[1] ⟶ pullback p b} (hf : IsCartesianEdge (pullback.snd p b) f) :
    IsLocallyCartesianEdge p (f ≫ pullback.fst p b) := by
  have hc : (f ≫ pullback.snd p b) ≫ b = (f ≫ pullback.fst p b) ≫ p := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  refine IsCartesianEdge.of_isPullback (isPullback_pullbackMap p b _ _ hc) ?_
  convert hf using 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMap_fst, pullback.lift_fst]
  · rw [Category.assoc, pullbackMap_snd, pullback.lift_snd_assoc, Category.id_comp]

private lemma δ_zero_σ_zero : (stdSimplex.δ 0 ≫ stdSimplex.σ 0 : Δ[1] ⟶ Δ[1]) = 𝟙 Δ[1] :=
  stdSimplex.δ_comp_σ_self' (n := 1) (j := 0) (i := 0) rfl

private lemma δ_one_σ_zero : (stdSimplex.δ 1 ≫ stdSimplex.σ 0 : Δ[1] ⟶ Δ[1]) = 𝟙 Δ[1] :=
  stdSimplex.δ_comp_σ_succ' (n := 1) (j := 1) (i := 0) rfl

private lemma δ_two_σ_zero :
    (stdSimplex.δ 2 ≫ stdSimplex.σ 0 : Δ[1] ⟶ Δ[1]) = stdSimplex.σ 0 ≫ stdSimplex.δ 1 :=
  stdSimplex.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by decide)

private lemma nonempty_invStruct_of_isCartesianEdge_of_comp_eq {Y K : SSet.{u}}
    [K.Quasicategory] (q : Y ⟶ K) [InnerFibration q] {α : Δ[1] ⟶ Y} (hα : IsCartesianEdge q α)
    (k : Δ[0] ⟶ K) (hk : α ≫ q = stdSimplex.σ 0 ≫ k) :
    Nonempty (Edge.mk' (yonedaEquiv α)).InvStruct :=
  have := quasicategory_of_innerFibration q
  (invStruct_iff_isCartesianEdge q α).2 ⟨hα, ⟨(Edge.InvStruct.invStructId (yonedaEquiv k)).ofEq (by
    rw [Edge.mk'_edge, Edge.id_edge, hk]
    exact yonedaEquiv.symm.injective (by
      rw [← stdSimplex.σ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]))⟩⟩

private lemma exists_isCartesianEdge_pullback [InnerFibration p] {e : Δ[1] ⟶ X} (σ : Δ[2] ⟶ X)
    (hσ : σ ≫ p = stdSimplex.σ 0 ≫ e ≫ p) (h₁ : stdSimplex.δ 1 ≫ σ = e)
    (h₀ : IsCartesianEdge p (stdSimplex.δ 0 ≫ σ)) (he : IsLocallyCartesianEdge p e) :
    ∃ α : Δ[1] ⟶ pullback p (e ≫ p), α ≫ pullback.fst _ _ = stdSimplex.δ 2 ≫ σ ∧
      α ≫ pullback.snd _ _ = stdSimplex.σ 0 ≫ stdSimplex.δ 1 ∧
      IsCartesianEdge (pullback.snd p (e ≫ p)) α := by
  let σ' := pullback.lift σ (stdSimplex.σ 0) hσ
  refine ⟨stdSimplex.δ 2 ≫ σ', by rw [Category.assoc, pullback.lift_fst], ?_,
    (isCartesianEdge_δ_two_iff_δ_one _ σ' ?_).2 ?_⟩
  · rw [Category.assoc, pullback.lift_snd]
    exact δ_two_σ_zero
  · exact IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback _ _)
      (by rwa [Category.assoc, pullback.lift_fst])
  · have he' : IsCartesianEdge (pullback.snd p (e ≫ p)) _ := he
    convert he' using 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact δ_one_σ_zero

private lemma exists_simplex_two {f e : Δ[1] ⟶ X} (hf : IsCartesianEdge p f)
    (ht : stdSimplex.δ 0 ≫ e = stdSimplex.δ 0 ≫ f) (τ : Δ[2] ⟶ S)
    (h₀ : stdSimplex.δ 0 ≫ τ = f ≫ p) (h₁ : stdSimplex.δ 1 ≫ τ = e ≫ p) :
    ∃ σ : Δ[2] ⟶ X, stdSimplex.δ 0 ≫ σ = f ∧ stdSimplex.δ 1 ≫ σ = e ∧ σ ≫ p = τ := by
  obtain ⟨σ, hσ₀, hσ₁, hσ⟩ := exists_simplex_two_of_isCartesianEdge hf (yonedaEquiv e)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, ht, stdSimplex.yonedaEquiv_δ_comp]) (yonedaEquiv τ)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₀, yonedaEquiv_comp])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, h₁, yonedaEquiv_comp])
  refine ⟨yonedaEquiv.symm σ, ?_, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, hσ₀, Equiv.symm_apply_apply]
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm, hσ₁, Equiv.symm_apply_apply]
  · rw [yonedaEquiv_symm_comp, hσ, Equiv.symm_apply_apply]

theorem exists_invStruct_fiber_of_isCartesianEdge [InnerFibration p] (σ : X _⦋2⦌)
    (hσ : p.app _ σ = S.σ 0 (S.δ 1 (p.app _ σ)))
    (h₀ : IsCartesianEdge p (yonedaEquiv.symm (X.δ 0 σ)))
    (h₁ : IsCartesianEdge p (yonedaEquiv.symm (X.δ 1 σ))) :
    ∃ α : (pullback p (yonedaEquiv.symm (S.δ 1 (S.δ 1 (p.app _ σ))))) _⦋1⦌,
      (pullback.fst p _).app _ α = X.δ 2 σ ∧ Nonempty (Edge.mk' α).InvStruct := by
  have hσ' : yonedaEquiv.symm σ ≫ p =
      stdSimplex.σ 0 ≫ yonedaEquiv.symm (X.δ 1 σ) ≫ p := by
    rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, stdSimplex.σ_comp_yonedaEquiv_symm,
      δ_naturality_apply]
    exact congrArg _ hσ
  obtain ⟨α, hα₁, hα₂, hα⟩ := exists_isCartesianEdge_pullback p _ hσ'
    (stdSimplex.δ_comp_yonedaEquiv_symm _ _)
    (by rwa [stdSimplex.δ_comp_yonedaEquiv_symm]) h₁.isLocallyCartesianEdge
  have hv : stdSimplex.δ 1 ≫ yonedaEquiv.symm (X.δ 1 σ) ≫ p =
      yonedaEquiv.symm (S.δ 1 (S.δ 1 (p.app _ σ))) := by
    rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, δ_naturality_apply]
  have sq := isPullback_pullbackMap p _ _ _ hv
  have hc := IsCartesianEdge.of_isPullback sq (f := sq.lift α (stdSimplex.σ 0) hα₂)
    (by rwa [sq.lift_fst])
  refine ⟨yonedaEquiv (sq.lift α (stdSimplex.σ 0) hα₂), ?_,
    nonempty_invStruct_of_isCartesianEdge_of_comp_eq _ hc (𝟙 _)
      (by rw [sq.lift_snd, Category.comp_id])⟩
  rw [← yonedaEquiv_comp, ← pullbackMap_fst p _ _ _ hv, ← Category.assoc, sq.lift_fst, hα₁,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]

theorem IsCartesianEdge.of_isLocallyCartesianEdge [InnerFibration p] {e e₀ : Δ[1] ⟶ X}
    (he₀ : IsCartesianEdge p e₀) (hp : e₀ ≫ p = e ≫ p)
    (ht : stdSimplex.δ 0 ≫ e₀ = stdSimplex.δ 0 ≫ e) (he : IsLocallyCartesianEdge p e) :
    IsCartesianEdge p e := by
  obtain ⟨σ, hσ₀, hσ₁, hσ⟩ := exists_simplex_two p he₀ ht.symm (stdSimplex.σ 0 ≫ e ≫ p)
    (by rw [← Category.assoc, δ_zero_σ_zero, Category.id_comp, hp])
    (by rw [← Category.assoc, δ_one_σ_zero, Category.id_comp])
  obtain ⟨α, hα₁, hα₂, hα⟩ := exists_isCartesianEdge_pullback p σ hσ hσ₁ (by rwa [hσ₀]) he
  refine (isCartesianEdge_iff_forall_pullback p e).2 fun n b f' hf' ↦ ?_
  have hℓ : (f' ≫ pullback.snd p b) ≫ b = e ≫ p := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hf']
  let σb := pullback.lift σ (stdSimplex.σ 0 ≫ f' ≫ pullback.snd p b) (by
    rw [hσ, Category.assoc, hℓ])
  have hg : IsCartesianEdge (pullback.snd p b) (stdSimplex.δ 0 ≫ σb) :=
    IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback p b)
      (by rwa [Category.assoc, pullback.lift_fst, hσ₀])
  have hf : IsCartesianEdge (pullback.snd p b) (stdSimplex.δ 2 ≫ σb) := by
    have hm : α ≫ pullbackMap p b _ _ hℓ = stdSimplex.δ 2 ≫ σb := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackMap_fst, hα₁, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, pullbackMap_snd, reassoc_of% hα₂, Category.assoc, pullback.lift_snd,
          ← Category.assoc (stdSimplex.δ 2), δ_two_σ_zero, Category.assoc]
    obtain ⟨I⟩ := nonempty_invStruct_of_isCartesianEdge_of_comp_eq _ hα _ hα₂
    have := quasicategory_of_innerFibration (pullback.snd p b)
    refine isCartesianEdge_of_invStruct _ ⟨(I.map (pullbackMap p b _ _ hℓ)).ofEq ?_⟩
    rw [Edge.map_edge, Edge.mk'_edge, Edge.mk'_edge, ← yonedaEquiv_comp, hm]
  have h := (isCartesianEdge_δ_two_iff_δ_one _ σb hg).1 hf
  convert h using 1
  apply pullback.hom_ext
  · rw [hf', Category.assoc, pullback.lift_fst, hσ₁]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, δ_one_σ_zero, Category.id_comp]

end Locality

class IsCartesianFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop extends InnerFibration p where
  exists_isCartesianEdge (y : X _⦋0⦌) (f : Δ[1] ⟶ S)
    (hf : stdSimplex.δ 0 ≫ f = yonedaEquiv.symm (p.app _ y)) :
    ∃ f' : Δ[1] ⟶ X, f' ≫ p = f ∧ stdSimplex.δ 0 ≫ f' = yonedaEquiv.symm y ∧
      IsCartesianEdge p f'

instance isCartesianFibration_of_isIso {X S : SSet.{u}} (p : X ⟶ S) [IsIso p] :
    IsCartesianFibration p where
  mem := innerFibrations.of_isIso p
  exists_isCartesianEdge y f hf := ⟨f ≫ inv p, by simp, by
    rw [← Category.assoc, hf, ← yonedaEquiv_symm_comp, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id], isCartesianEdge_of_isIso p _⟩

theorem IsCartesianFibration.of_isPullback {X S X' S' : SSet.{u}} {p : X ⟶ S} {p' : X' ⟶ S'}
    {q : X' ⟶ X} {g : S' ⟶ S} (h : IsPullback q p' p g) [IsCartesianFibration p] :
    IsCartesianFibration p' where
  mem := innerFibrations.of_isPullback h (mem_innerFibrations p)
  exists_isCartesianEdge y f hf := by
    obtain ⟨f', hf'p, hf'y, hf'⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p)
      (q.app _ y) (f ≫ g) (by
        rw [← Category.assoc, hf, yonedaEquiv_symm_comp]
        exact congrArg _ (ConcreteCategory.congr_hom (congr_app h.w _) y).symm)
    refine ⟨h.lift f' f hf'p, h.lift_snd _ _ _, h.hom_ext ?_ ?_, ?_⟩
    · rw [Category.assoc, h.lift_fst, hf'y, yonedaEquiv_symm_comp]
    · rw [Category.assoc, h.lift_snd, hf, yonedaEquiv_symm_comp]
    · exact IsCartesianEdge.of_isPullback h (by rwa [h.lift_fst])

instance isCartesianFibration_comp {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [IsCartesianFibration p] [IsCartesianFibration q] : IsCartesianFibration (p ≫ q) where
  mem := innerFibrations.comp_mem _ _ (mem_innerFibrations p) (mem_innerFibrations q)
  exists_isCartesianEdge y f hf := by
    obtain ⟨g', hg'q, hg'y, hg'⟩ := IsCartesianFibration.exists_isCartesianEdge (p := q)
      (p.app _ y) f hf
    obtain ⟨f', hf'p, hf'y, hf'⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p) y g' hg'y
    exact ⟨f', by rw [← Category.assoc, hf'p, hg'q], hf'y, hf'.comp (by rwa [hf'p])⟩

theorem IsCartesianFibration.isCartesianEdge_iff {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] (e : Δ[1] ⟶ X) :
    IsCartesianEdge p e ↔ IsLocallyCartesianEdge p e := by
  refine ⟨IsCartesianEdge.isLocallyCartesianEdge, fun he ↦ ?_⟩
  obtain ⟨e₀, h₁, h₂, h₃⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p)
    (yonedaEquiv (stdSimplex.δ 0 ≫ e)) (e ≫ p)
    (by rw [← yonedaEquiv_comp, Equiv.symm_apply_apply, Category.assoc])
  exact IsCartesianEdge.of_isLocallyCartesianEdge p h₃ h₁ (by rw [h₂, Equiv.symm_apply_apply]) he

theorem IsCartesianFibration.isCartesianEdge_id {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] (x : Δ[0] ⟶ X) : IsCartesianEdge p (stdSimplex.σ 0 ≫ x) := by
  rw [isCartesianEdge_iff]
  refine IsCartesianEdge.of_isPullback
    (isPullback_pullbackMap p _ _ _ (Category.assoc _ _ _).symm) ?_
  let x' : Δ[0] ⟶ pullback p (x ≫ p) := pullback.lift x (𝟙 Δ[0]) (Category.id_comp _).symm
  have := quasicategory_of_innerFibration (pullback.snd p (x ≫ p))
  have h := SSet.isCartesianEdge_id (pullback.snd p (x ≫ p)) (yonedaEquiv x')
  rw [Edge.id_edge, ← stdSimplex.σ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply] at h
  convert h using 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMap_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, pullbackMap_snd, pullback.lift_snd_assoc, Category.assoc,
      pullback.lift_snd, Category.id_comp, Category.comp_id]

theorem IsCartesianFibration.isCartesianEdge_δ_two_iff_δ_one {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] (σ : X _⦋2⦌) (hg : IsCartesianEdge p (yonedaEquiv.symm (X.δ 0 σ))) :
    IsCartesianEdge p (yonedaEquiv.symm (X.δ 2 σ)) ↔
      IsCartesianEdge p (yonedaEquiv.symm (X.δ 1 σ)) := by
  simp only [← stdSimplex.δ_comp_yonedaEquiv_symm] at hg ⊢
  let σ' := pullback.lift (yonedaEquiv.symm σ) (𝟙 Δ[2])
    (Category.id_comp (yonedaEquiv.symm σ ≫ p)).symm
  have key (i : Fin 3) : IsCartesianEdge p (stdSimplex.δ i ≫ yonedaEquiv.symm σ) ↔
      IsCartesianEdge (pullback.snd p (yonedaEquiv.symm σ ≫ p)) (stdSimplex.δ i ≫ σ') := by
    refine ⟨fun h ↦ IsCartesianEdge.of_isPullback (IsPullback.of_hasPullback _ _)
      (by rwa [Category.assoc, pullback.lift_fst]), fun h ↦ (isCartesianEdge_iff p _).2 ?_⟩
    have h' := isLocallyCartesianEdge_of_pullback p _ h
    rwa [Category.assoc, pullback.lift_fst] at h'
  rw [key 2, key 1]
  exact SSet.isCartesianEdge_δ_two_iff_δ_one _ σ' ((key 0).1 hg)

private lemma hasLiftingProperty_horn_one_one_iff {X S : SSet.{u}} (p : X ⟶ S) :
    HasLiftingProperty Λ[1, 1].ι p ↔ ∀ (y : X _⦋0⦌) (f : Δ[1] ⟶ S),
      stdSimplex.δ 0 ≫ f = yonedaEquiv.symm (p.app _ y) →
        ∃ f' : Δ[1] ⟶ X, f' ≫ p = f ∧ stdSimplex.δ 0 ≫ f' = yonedaEquiv.symm y := by
  refine ⟨fun h y f hf ↦ ?_, fun h ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
  · have hc : horn.IsCompatible (i := (1 : Fin 2))
        (fun _ _ ↦ (yonedaEquiv.symm y : Δ[0] ⟶ X)) := trivial
    have hsq : CommSq hc.desc Λ[1, 1].ι p f := ⟨horn.hom_ext' fun j hj ↦ by
      rw [hc.ι_desc_assoc, horn.ι_ι_assoc, yonedaEquiv_symm_comp]
      obtain rfl : j = 0 := by
        fin_cases j
        · rfl
        · exact (hj rfl).elim
      exact hf.symm⟩
    obtain ⟨l⟩ := (h.sq_hasLift hsq).exists_lift
    exact ⟨l.l, l.fac_right, by rw [← horn.ι_ι 1 0 (by decide), Category.assoc, l.fac_left,
      hc.ι_desc]⟩
  · have h10 : (0 : Fin 2) ≠ 1 := by decide
    obtain ⟨f', hf'p, hf'y⟩ := h (yonedaEquiv (horn.ι 1 0 h10 ≫ a)) b (by
      rw [← yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.assoc, sq.w, ← horn.ι_ι_assoc])
    refine ⟨⟨⟨f', horn.hom_ext' fun j hj ↦ ?_, hf'p⟩⟩⟩
    obtain rfl : j = 0 := by
      fin_cases j
      · rfl
      · exact (hj rfl).elim
    rw [horn.ι_ι_assoc, hf'y, Equiv.symm_apply_apply]

theorem rightFibrations_iff_isCartesianFibration_and_forall {X S : SSet.{u}} (p : X ⟶ S) :
    rightFibrations p ↔ IsCartesianFibration p ∧ ∀ f : Δ[1] ⟶ X, IsCartesianEdge p f := by
  have hlast (n : ℕ) : Fin.last (n + 2) ≠ 0 := Fin.last_pos.ne'
  refine ⟨fun hp ↦ ?_, fun ⟨hcf, hall⟩ ↦ ?_⟩
  · have hall (f : Δ[1] ⟶ X) : IsCartesianEdge p f :=
      (isCartesianEdge_iff_hasLift_horn p f).2 fun _ _ _ sq _ ↦
        (hp _ (horn_ι_mem_rightHornInclusions Fin.last_pos)).sq_hasLift sq
    have := innerFibration_of_rightFibrations hp
    refine ⟨⟨fun y f hf ↦ ?_⟩, hall⟩
    obtain ⟨f', h₁, h₂⟩ := (hasLiftingProperty_horn_one_one_iff p).1
      (hp _ (horn_ι_mem_rightHornInclusions (by decide))) y f hf
    exact ⟨f', h₁, h₂, hall f'⟩
  · rintro _ _ _ ⟨i, h0⟩
    rename_i n
    by_cases hi : i = Fin.last (n + 1)
    · subst hi
      obtain _ | n := n
      · exact (hasLiftingProperty_horn_one_one_iff p).2 fun y f hf ↦
          (hcf.exists_isCartesianEdge y f hf).imp fun _ h ↦ ⟨h.1, h.2.1⟩
      · exact ⟨fun sq ↦ (isCartesianEdge_iff_hasLift_horn p _).1 (hall _) n _ _ sq
          (Equiv.apply_symm_apply _ _).symm⟩
    · exact hcf.mem _ (horn_ι_mem_innerHornInclusions h0
        (lt_of_le_of_ne (Fin.le_last i) hi))

theorem IsCartesianFibration.of_rightFibrations {X S : SSet.{u}} {p : X ⟶ S}
    (hp : rightFibrations p) : IsCartesianFibration p :=
  ((rightFibrations_iff_isCartesianFibration_and_forall p).1 hp).1

private lemma isCartesianEdge_of_forall_invStruct {X S : SSet.{u}} [S.Quasicategory] (p : X ⟶ S)
    [IsCartesianFibration p]
    (h : ∀ (g : Δ[1] ⟶ X) (s : Δ[0] ⟶ S), g ≫ p = stdSimplex.σ 0 ≫ s →
      Nonempty (Edge.mk' (yonedaEquiv g)).InvStruct) (f : Δ[1] ⟶ X) : IsCartesianEdge p f := by
  have := quasicategory_of_innerFibration p
  obtain ⟨f', hf'p, hf'y, hf'⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p)
    (yonedaEquiv (stdSimplex.δ 0 ≫ f)) (f ≫ p)
    (by rw [← yonedaEquiv_comp, Equiv.symm_apply_apply, Category.assoc])
  rw [Equiv.symm_apply_apply] at hf'y
  have he : X.δ 0 (yonedaEquiv f) = X.δ 0 (yonedaEquiv f') := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp, hf'y]
  have h₀ : S.δ 0 (S.σ 0 (p.app _ (yonedaEquiv f))) = p.app _ (yonedaEquiv f') := by
    refine (δ_comp_σ_self_apply (S := S) (n := 1) 0 _).trans ?_
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, hf'p]
  obtain ⟨σ, hσ₀, hσ₁, hσ⟩ := exists_simplex_two_of_isCartesianEdge hf' (yonedaEquiv f) he
    (S.σ 0 (p.app _ (yonedaEquiv f))) h₀ (δ_comp_σ_succ_apply (S := S) 0 _)
  have hg := isCartesianEdge_of_invStruct p (h (stdSimplex.δ 2 ≫ yonedaEquiv.symm σ)
    (yonedaEquiv.symm (S.δ 1 (p.app _ (yonedaEquiv f)))) (by
      rw [Category.assoc, yonedaEquiv_symm_comp, hσ, stdSimplex.δ_comp_yonedaEquiv_symm,
        stdSimplex.σ_comp_yonedaEquiv_symm]
      exact congrArg _ (δ_comp_σ_of_gt_apply (S := S) (n := 0) (i := 1) (j := 0) (by decide) _)))
  have h₁ := (isCartesianEdge_δ_two_iff_δ_one p (yonedaEquiv.symm σ) (by
    rwa [stdSimplex.δ_comp_yonedaEquiv_symm, hσ₀, Equiv.symm_apply_apply])).1 hg
  rwa [stdSimplex.δ_comp_yonedaEquiv_symm, hσ₁, Equiv.symm_apply_apply] at h₁

theorem rightFibrations_of_isCartesianFibration_of_kanComplex {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p]
    (h : ∀ s : S _⦋0⦌, (pullback p (yonedaEquiv.symm s : Δ[0] ⟶ S)).KanComplex) :
    rightFibrations p := by
  refine (rightFibrations_iff_isCartesianFibration_and_forall p).2 ⟨inferInstance, fun f ↦
    (isCartesianEdge_iff_forall_pullback p f).2 fun n b f' _ ↦ ?_⟩
  have := IsCartesianFibration.of_isPullback (IsPullback.of_hasPullback p b)
  refine isCartesianEdge_of_forall_invStruct (pullback.snd p b) (fun g v hg ↦ ?_) f'
  have hK := h (yonedaEquiv (v ≫ b))
  rw [Equiv.symm_apply_apply] at hK
  have hF : (g ≫ pullback.fst p b) ≫ p = stdSimplex.σ 0 ≫ v ≫ b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg, Category.assoc]
  let m : pullback p (v ≫ b) ⟶ pullback p b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ v) (by
      rw [pullback.condition, Category.assoc])
  have hm : pullback.lift _ _ hF ≫ m = g := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hg]
  obtain ⟨I⟩ := nonempty_invStruct_of_kanComplex _ (yonedaEquiv (pullback.lift _ _ hF))
  exact ⟨(I.map m).ofEq (by rw [Edge.map_edge, Edge.mk'_edge, Edge.mk'_edge, ← yonedaEquiv_comp,
    hm])⟩

def cartesianSubcomplex {X S : SSet.{u}} (p : X ⟶ S) : X.Subcomplex where
  obj n := {σ | ∀ f : ⦋1⦌ ⟶ n.unop, IsCartesianEdge p (yonedaEquiv.symm (X.map f.op σ))}
  map g σ hσ f := by
    simpa only [Set.mem_ofPred_eq, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]
      using hσ (f ≫ g.unop)

theorem mem_cartesianSubcomplex_iff {X S : SSet.{u}} (p : X ⟶ S) {n : ℕ} (σ : X _⦋n⦌) :
    σ ∈ (cartesianSubcomplex p).obj _ ↔
      ∀ f : ⦋1⦌ ⟶ ⦋n⦌, IsCartesianEdge p (stdSimplex.map f ≫ yonedaEquiv.symm σ) := by
  simp only [yonedaEquiv_symm_naturality_left]
  rfl

section CartesianSubcomplex

variable {X S : SSet.{u}} (p : X ⟶ S)

private lemma isCartesianEdge_comp_ι (f : Δ[1] ⟶ cartesianSubcomplex p) :
    IsCartesianEdge p (f ≫ (cartesianSubcomplex p).ι) := by
  have h := (yonedaEquiv f).2 (𝟙 _)
  simp only [op_id, Functor.map_id_apply] at h
  have e : (yonedaEquiv f).1 = yonedaEquiv (f ≫ (cartesianSubcomplex p).ι) := rfl
  rwa [e, Equiv.symm_apply_apply] at h

private lemma isCartesianEdge_of_horn {m : ℕ} {k : Fin (m + 2)} {l : Δ[m + 1] ⟶ X}
    {a : (Λ[m + 1, k] : SSet.{u}) ⟶ cartesianSubcomplex p}
    (ha : Λ[m + 1, k].ι ≫ l = a ≫ (cartesianSubcomplex p).ι) (f : ⦋1⦌ ⟶ ⦋m + 1⦌)
    (j : Fin (m + 2)) (hj : j ≠ k) (hf : ∀ x, f.toOrderHom x ≠ j) :
    IsCartesianEdge p (stdSimplex.map f ≫ l) := by
  obtain ⟨θ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' f j hf
  have h : stdSimplex.map (θ ≫ SimplexCategory.δ j) ≫ l =
      (stdSimplex.map θ ≫ horn.ι k j hj ≫ a) ≫ (cartesianSubcomplex p).ι := by
    rw [Category.assoc, Category.assoc, ← ha, horn.ι_ι_assoc]
    exact (congrArg (· ≫ l) (Functor.map_comp stdSimplex θ _)).trans (Category.assoc _ _ _)
  rw [h]
  exact isCartesianEdge_comp_ι p _

private lemma isCartesianEdge_δ_iff (σ : Δ[2] ⟶ X) (i : Fin 3) :
    IsCartesianEdge p (stdSimplex.δ i ≫ σ) ↔
      IsCartesianEdge p (yonedaEquiv.symm (X.δ i (yonedaEquiv σ))) := by
  rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]

private lemma exists_ne_of_three_le {n : ℕ} (hn : 3 ≤ n) (f : ⦋1⦌ ⟶ ⦋n⦌) (k : Fin (n + 1)) :
    ∃ j, j ≠ k ∧ ∀ x, f.toOrderHom x ≠ j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {f.toOrderHom 0, f.toOrderHom 1, k}) (t := Finset.univ)
    (Finset.card_le_three.trans_lt (by rw [Finset.card_univ, Fintype.card_fin]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  refine ⟨j, hj.2.2, fun x hx ↦ ?_⟩
  fin_cases x
  · exact hj.1 hx.symm
  · exact hj.2.1 hx.symm

private lemma eq_δ_of_forall {k : Fin 3} (f : ⦋1⦌ ⟶ ⦋2⦌)
    (h : ∀ j, j ≠ k → ∃ x, f.toOrderHom x = j) : f = SimplexCategory.δ k := by
  have key : ∀ a b k : Fin 3, a ≤ b → (∀ j, j ≠ k → j = a ∨ j = b) →
      a = k.succAbove 0 ∧ b = k.succAbove 1 := by decide
  obtain ⟨h₀, h₁⟩ := key _ _ k (f.toOrderHom.monotone (by decide : (0 : Fin 2) ≤ 1)) fun j hj ↦ by
    obtain ⟨x, hx⟩ := h j hj
    fin_cases x
    · exact Or.inl hx.symm
    · exact Or.inr hx.symm
  ext x : 3
  fin_cases x
  · exact h₀
  · exact h₁

private lemma exists_lift_cartesianSubcomplex {n : ℕ} (l : Δ[n] ⟶ X)
    (hl : ∀ f : ⦋1⦌ ⟶ ⦋n⦌, IsCartesianEdge p (stdSimplex.map f ≫ l)) :
    ∃ l' : Δ[n] ⟶ cartesianSubcomplex p, l' ≫ (cartesianSubcomplex p).ι = l :=
  ⟨Subcomplex.lift l (by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, mem_cartesianSubcomplex_iff,
      Equiv.symm_apply_apply]
    exact hl), Subcomplex.lift_ι _ _⟩

private lemma innerFibration_cartesianSubcomplex [IsCartesianFibration p] :
    InnerFibration ((cartesianSubcomplex p).ι ≫ p) := by
  refine ⟨?_⟩
  rintro _ _ _ ⟨i, h0, hn⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨l⟩ := ((mem_innerFibrations p _ (.intro i h0 hn)).sq_hasLift
    (⟨by rw [Category.assoc, sq.w]⟩ : CommSq (a ≫ (cartesianSubcomplex p).ι) _ p b)).exists_lift
  obtain ⟨l', hl'⟩ := exists_lift_cartesianSubcomplex p l.l fun g ↦ by
    by_cases hg : ∃ j, j ≠ i ∧ ∀ x, g.toOrderHom x ≠ j
    · obtain ⟨j, hj, hgj⟩ := hg
      exact isCartesianEdge_of_horn p l.fac_left g j hj hgj
    rename_i n
    obtain _ | n := n
    · obtain rfl : i = 1 := (by decide : ∀ i : Fin 3, 0 < i → i < Fin.last 2 → i = 1) i h0 hn
      push Not at hg
      rw [eq_δ_of_forall g hg]
      refine (isCartesianEdge_δ_iff p l.l _).2
        ((IsCartesianFibration.isCartesianEdge_δ_two_iff_δ_one p _ ((isCartesianEdge_δ_iff p _ _).1
          (isCartesianEdge_of_horn p l.fac_left _ 0 (by decide) (Fin.succAbove_ne 0)))).1
            ((isCartesianEdge_δ_iff p _ _).1
              (isCartesianEdge_of_horn p l.fac_left _ 2 (by decide) (Fin.succAbove_ne 2))))
    · exact absurd (exists_ne_of_three_le (by omega) g i) hg
  refine ⟨⟨⟨l', (cancel_mono (cartesianSubcomplex p).ι).1 ?_, ?_⟩⟩⟩
  · rw [Category.assoc, hl', l.fac_left]
  · rw [← Category.assoc, hl', l.fac_right]

private lemma isCartesianEdge_cartesianSubcomplex [IsCartesianFibration p]
    (f : Δ[1] ⟶ cartesianSubcomplex p) : IsCartesianEdge ((cartesianSubcomplex p).ι ≫ p) f := by
  refine (isCartesianEdge_iff_hasLift_horn _ f).2 fun n a b sq ha ↦ ?_
  obtain ⟨l⟩ := ((isCartesianEdge_iff_hasLift_horn p _).1 (isCartesianEdge_comp_ι p f) n
    (a ≫ (cartesianSubcomplex p).ι) b ⟨by rw [Category.assoc, sq.w]⟩
    ((congrArg ((cartesianSubcomplex p).ι.app _) ha).trans (yonedaEquiv_comp _ _).symm)).exists_lift
  obtain ⟨l', hl'⟩ := exists_lift_cartesianSubcomplex p l.l fun g ↦ by
    by_cases hg : ∃ j, j ≠ Fin.last (n + 2) ∧ ∀ x, g.toOrderHom x ≠ j
    · obtain ⟨j, hj, hgj⟩ := hg
      exact isCartesianEdge_of_horn p l.fac_left g j hj hgj
    obtain _ | n := n
    · push Not at hg
      rw [eq_δ_of_forall g hg]
      refine (isCartesianEdge_δ_iff p l.l _).2
        ((IsCartesianFibration.isCartesianEdge_δ_two_iff_δ_one p _ ((isCartesianEdge_δ_iff p _ _).1
          (isCartesianEdge_of_horn p l.fac_left _ 0 (by decide) (Fin.succAbove_ne 0)))).2
            ((isCartesianEdge_δ_iff p _ _).1
              (isCartesianEdge_of_horn p l.fac_left _ 1 (by decide) (Fin.succAbove_ne 1))))
    · exact absurd (exists_ne_of_three_le (by omega) g _) hg
  refine ⟨⟨⟨l', (cancel_mono (cartesianSubcomplex p).ι).1 ?_, ?_⟩⟩⟩
  · rw [Category.assoc, hl', l.fac_left]
  · rw [← Category.assoc, hl', l.fac_right]

private lemma isCartesianEdge_map_comp [IsCartesianFibration p]
    {f : Δ[1] ⟶ X} (hf : IsCartesianEdge p f) (g : ⦋1⦌ ⟶ ⦋1⦌) :
    IsCartesianEdge p (stdSimplex.map g ≫ f) := by
  by_cases hg : ∃ j, ∀ x, g.toOrderHom x ≠ j
  · obtain ⟨j, hj⟩ := hg
    obtain ⟨θ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' g j hj
    obtain rfl : θ = SimplexCategory.σ 0 := by
      ext x : 3
      exact Subsingleton.elim (α := Fin 1) _ _
    have h := IsCartesianFibration.isCartesianEdge_id p (stdSimplex.δ j ≫ f)
    rw [← Category.assoc] at h
    exact (congrArg (fun φ ↦ IsCartesianEdge p (φ ≫ f)) (Functor.map_comp stdSimplex _ _)).mpr h
  · push Not at hg
    have := SimplexCategory.epi_iff_surjective.2 fun j ↦ hg j
    obtain rfl := SimplexCategory.eq_id_of_epi g
    exact (congrArg (fun φ ↦ IsCartesianEdge p (φ ≫ f))
      (CategoryTheory.Functor.map_id stdSimplex _)).mpr ((Category.id_comp f).symm ▸ hf)

end CartesianSubcomplex

theorem rightFibrations_cartesianSubcomplex {X S : SSet.{u}} (p : X ⟶ S)
    [IsCartesianFibration p] :
    rightFibrations ((cartesianSubcomplex p).ι ≫ p) := by
  have := innerFibration_cartesianSubcomplex p
  refine (rightFibrations_iff_isCartesianFibration_and_forall _).2
    ⟨⟨fun y f hf ↦ ?_⟩, isCartesianEdge_cartesianSubcomplex p⟩
  obtain ⟨f', hf'p, hf'y, hf'⟩ := IsCartesianFibration.exists_isCartesianEdge (p := p)
    ((cartesianSubcomplex p).ι.app _ y) f hf
  obtain ⟨f'', hf''⟩ := exists_lift_cartesianSubcomplex p f' (isCartesianEdge_map_comp p hf')
  refine ⟨f'', by rw [← Category.assoc, hf'', hf'p], (cancel_mono (cartesianSubcomplex p).ι).1 ?_,
    isCartesianEdge_cartesianSubcomplex p f''⟩
  rw [Category.assoc, hf'', hf'y, yonedaEquiv_symm_comp]

end SSet
