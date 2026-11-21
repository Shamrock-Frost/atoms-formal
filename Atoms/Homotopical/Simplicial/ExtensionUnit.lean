import Atoms.ForMathlib.CategoryTheory.Subfunctor.Image
import Atoms.Homotopical.Simplicial.ChainMaps
import Atoms.Homotopical.Simplicial.Subdivision
import Atoms.Homotopical.Simplicial.PairingRestriction

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

noncomputable def exRelativeUnit {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ pullback (exUnit.app Y) (SSet.ex.map f) :=
  pullback.lift f (exUnit.app X) (exUnit.naturality f)

namespace MossUnit

open PartialOrder

variable {X : SSet.{u}}

def exHom {m : ℕ} (σ : (SSet.ex.obj X) _⦋m⦌) : SimplexCategory.sd.obj ⦋m⦌ ⟶ X :=
  ULift.down σ

def exMk {m : ℕ} (g : SimplexCategory.sd.obj ⦋m⦌ ⟶ X) : (SSet.ex.obj X) _⦋m⦌ :=
  ULift.up g

noncomputable def sdHom {n m : ℕ} (φ : Chains n →o Chains m) :
    SimplexCategory.sd.{u}.obj ⦋n⦌ ⟶ SimplexCategory.sd.obj ⦋m⦌ :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom φ)

noncomputable def act {n m : ℕ} (σ : (SSet.ex.obj X) _⦋m⦌) (φ : Chains n →o Chains m) :
    (SSet.ex.obj X) _⦋n⦌ :=
  exMk (sdHom φ ≫ exHom σ)

theorem act_act {n m l : ℕ} (σ : (SSet.ex.obj X) _⦋l⦌) (φ : Chains m →o Chains l)
    (ψ : Chains n →o Chains m) : act (act σ φ) ψ = act σ (φ.comp ψ) := by
  unfold act
  congr 1

theorem act_id {n : ℕ} (σ : (SSet.ex.obj X) _⦋n⦌) : act σ OrderHom.id = σ := by
  unfold act
  congr 1

theorem δ_eq_act {n : ℕ} (i : Fin (n + 2)) (σ : (SSet.ex.obj X) _⦋n + 1⦌) :
    (SSet.ex.obj X).δ i σ = act σ (sdCoface n i.val) := by
  rw [← orderHomMap_δ]
  rfl

theorem σ_eq_act {n : ℕ} (i : Fin (n + 1)) (σ : (SSet.ex.obj X) _⦋n⦌) :
    (SSet.ex.obj X).σ i σ = act σ (sdCodegeneracy n i.val (Nat.lt_succ_iff.1 i.isLt)) := by
  rw [← orderHomMap_σ]
  rfl

theorem ex_map_act {Y : SSet.{u}} (f : X ⟶ Y) {n m : ℕ} (σ : (SSet.ex.obj X) _⦋m⦌)
    (φ : Chains n →o Chains m) :
    (SSet.ex.map f).app _ (act σ φ) = act ((SSet.ex.map f).app _ σ) φ := by
  change exMk ((sdHom φ ≫ exHom σ) ≫ f) = exMk (sdHom φ ≫ exHom σ ≫ f)
  rw [Category.assoc]

variable (X) in
def fixedSimplices (n k : ℕ) : Set ((SSet.ex.obj X) _⦋n⦌) := {σ | act σ (jMap n k) = σ}

theorem jMap_of_le {n k : ℕ} (h : n ≤ k) : jMap n k = OrderHom.id := by
  apply orderHom_ext
  intro S
  change joinF (jGen n k) S.finset = S.finset
  conv_rhs => rw [← joinF_single_self S.finset]
  exact joinF_congr _ fun c hc ↦ jGen_of_le (by omega)

theorem mem_fixedSimplices_of_le {n k : ℕ} (h : n ≤ k) (σ : (SSet.ex.obj X) _⦋n⦌) : σ ∈
    fixedSimplices X n k := by
  change act σ _ = σ
  rw [jMap_of_le h, act_id]

theorem fixedSimplices_mono {n k l : ℕ} (h : k ≤ l) : fixedSimplices X n k ⊆ fixedSimplices X n l :=
    by
  intro σ hσ
  change act σ _ = σ
  change act σ _ = σ at hσ
  rw [← hσ, act_act, jMap_comp_jMap n k l h]

theorem δ_act_rMap {n k : ℕ} (hk : k ≤ n) (σ : (SSet.ex.obj X) _⦋n⦌) :
    (SSet.ex.obj X).δ ⟨k + 1, by omega⟩ (act σ (rMap n k hk)) = σ := by
  rw [δ_eq_act, act_act]
  change act σ ((rMap n k hk).comp (sdCoface n (k + 1))) = σ
  rw [rMap_comp_sdCoface, act_id]

theorem act_rMap_mem_fixedSimplices {n k h : ℕ} (hk : k ≤ n) (hh : h ≤ k) {σ : (SSet.ex.obj X) _⦋n⦌}
    (hσ : σ ∈ fixedSimplices X n h) : act σ (rMap n k hk) ∈ fixedSimplices X (n + 1) h := by
  change act _ _ = _
  change act σ _ = σ at hσ
  rw [act_act, rMap_comp_jMap n k h hk hh, ← act_act, hσ]

theorem act_sdCoface_mem_fixedSimplices {n k i : ℕ} {σ : (SSet.ex.obj X) _⦋n + 1⦌} (hσ : σ ∈
    fixedSimplices X (n + 1) k) :
    act σ (sdCoface n i) ∈ fixedSimplices X n k := by
  change act _ _ = _
  change act σ _ = σ at hσ
  conv_lhs => rw [← hσ]
  conv_rhs => rw [← hσ]
  rw [act_act, act_act, act_act]
  exact congrArg (act σ) (jMap_comp_sdCoface_comp_jMap n k i)

theorem act_rMap_sdCoface_mem_fixedSimplices {n k i : ℕ} (hk : k ≤ n) (hk1 : 1 ≤ k) (hi : i ≤ k)
    {σ : (SSet.ex.obj X) _⦋n⦌} (hσ : σ ∈ fixedSimplices X n k) :
    act (act σ (rMap n k hk)) (sdCoface n i) ∈ fixedSimplices X n (k - 1) := by
  change act _ _ = _
  change act σ _ = σ at hσ
  conv_lhs => rw [← hσ]
  conv_rhs => rw [← hσ]
  simp only [act_act]
  exact congrArg (act σ) (jMap_comp_rMap_comp_sdCoface_comp_jMap n k i hk hk1 hi)

theorem act_rMap_sdCoface_eq {m k i : ℕ} (hk : k ≤ m) (hi : k + 2 ≤ i)
    (σ : (SSet.ex.obj X) _⦋m + 1⦌) :
    act (act σ (rMap (m + 1) k (by omega))) (sdCoface (m + 1) i) =
      act (act σ (sdCoface m (i - 1))) (rMap m k hk) := by
  simp only [act_act]
  exact congrArg (act σ) (rMap_comp_sdCoface_of_lt m k i hk hi)

theorem act_rMap_eq_σ {m k : ℕ} (hk : k ≤ m) (hk1 : 1 ≤ k) {τ : (SSet.ex.obj X) _⦋m⦌}
    (hτ : τ ∈ fixedSimplices X m (k - 1)) :
    act τ (rMap m k hk) = (SSet.ex.obj X).σ ⟨k, by omega⟩ τ := by
  change act τ _ = τ at hτ
  rw [σ_eq_act]
  conv_lhs => rw [← hτ]
  conv_rhs => rw [← hτ]
  simp only [act_act]
  exact congrArg (act τ) (jMap_comp_rMap m k (k - 1) hk (by omega))

theorem act_rMap_rMap_eq_σ {m k : ℕ} (hk : k ≤ m) {τ : (SSet.ex.obj X) _⦋m⦌} (hτ : τ ∈
    fixedSimplices X m k) :
    act (act τ (rMap m k hk)) (rMap (m + 1) k (by omega)) =
      (SSet.ex.obj X).σ ⟨k + 1, by omega⟩ (act τ (rMap m k hk)) := by
  change act τ _ = τ at hτ
  rw [σ_eq_act]
  conv_lhs => rw [← hτ]
  conv_rhs => rw [← hτ]
  simp only [act_act]
  exact congrArg (act τ) (jMap_comp_rMap_comp_rMap m k hk)

theorem act_rMap_mem_degenerate {m k : ℕ} (hk : k ≤ m + 1) (h : Fin (m + 1))
    (τ : (SSet.ex.obj X) _⦋m⦌) (hσ : (SSet.ex.obj X).σ h τ ∈ fixedSimplices X (m + 1) k) :
    act ((SSet.ex.obj X).σ h τ) (rMap (m + 1) k hk) ∈ (SSet.ex.obj X).degenerate (m + 2) := by
  change act _ _ = _ at hσ
  rw [← hσ, act_act, σ_eq_act, act_act]
  obtain hhk | hhk := lt_or_ge h.val k
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sdCodegeneracy_comp_jMap_comp_rMap_succ m k h.val (by omega) (by omega), ← act_act, ←
        act_act,
      ← σ_eq_act (i := ⟨h.val, by omega⟩)]
    exact SSet.σ_mem_degenerate _ _ _
  · rw [sdCodegeneracy_comp_jMap_comp_rMap m k h.val (by omega) hhk (by omega), ← act_act, ←
      act_act,
      ← σ_eq_act (i := ⟨h.val + 1, by omega⟩)]
    exact SSet.σ_mem_degenerate _ _ _

theorem jMap_zero (n : ℕ) : jMap n 0 = (chainIic ⦋n⦌).comp (chainMax ⦋n⦌) := by
  apply orderHom_ext
  intro S
  ext x
  change x ∈ joinF (jGen n 0) S.finset ↔ x ∈ (chainIic ⦋n⦌ (chainMax ⦋n⦌ S)).finset
  rw [mem_chainIic, mem_joinF]
  have hmax : ∀ a ∈ S.finset, a ≤ chainMax ⦋n⦌ S := fun a ha ↦ Finset.le_max' _ _ ha
  constructor
  · rintro ⟨a, ha, hx⟩
    have h1 := hmax a ha
    rw [mem_jGen] at hx
    change x.down ≤ (chainMax ⦋n⦌ S).down
    change a.down ≤ (chainMax ⦋n⦌ S).down at h1
    rw [Fin.le_def] at h1 ⊢
    omega
  · intro hx
    refine ⟨chainMax ⦋n⦌ S, Finset.max'_mem S.finset S.nonempty, ?_⟩
    change x.down ≤ (chainMax ⦋n⦌ S).down at hx
    rw [Fin.le_def] at hx
    rw [mem_jGen]
    omega

theorem sdHom_jMap_zero_comp_simplexLastVertex (n : ℕ) :
    sdHom (jMap n 0) ≫ simplexLastVertex.app ⦋n⦌ = simplexLastVertex.app ⦋n⦌ := by
  have e : PartOrd.ofHom (jMap n 0) ≫ PartOrd.ofHom (chainMax ⦋n⦌) =
      PartOrd.ofHom (chainMax ⦋n⦌) := by
    refine congrArg PartOrd.ofHom (OrderHom.ext _ _ (funext fun S ↦ ?_))
    change chainMax ⦋n⦌ (jMap n 0 S) = chainMax ⦋n⦌ S
    rw [jMap_zero]
    exact chainMax_chainIic _ _
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (SSet.stdSimplex.isoNerve n).inv)
    ((PartOrd.nerveFunctor.map_comp _ _).symm.trans (congrArg PartOrd.nerveFunctor.map e)))

theorem sdHom_jMap_zero_comp {n : ℕ} (g : SimplexCategory.sd.obj ⦋n⦌ ⟶ X) :
    sdHom (jMap n 0) ≫ g = simplexLastVertex.app ⦋n⦌ ≫ (SSet.stdSimplex.isoNerve n).hom ≫
      PartOrd.nerveFunctor.map (PartOrd.ofHom (chainIic ⦋n⦌)) ≫ g := by
  have e : sdHom (jMap n 0) = PartOrd.nerveFunctor.map (PartOrd.ofHom (chainMax ⦋n⦌)) ≫
      PartOrd.nerveFunctor.map (PartOrd.ofHom (chainIic ⦋n⦌)) := by
    rw [sdHom, jMap_zero]
    exact PartOrd.nerveFunctor.map_comp (PartOrd.ofHom (chainMax ⦋n⦌))
      (PartOrd.ofHom (chainIic ⦋n⦌))
  refine (congrArg (· ≫ g) e).trans ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (PartOrd.nerveFunctor.map (PartOrd.ofHom (chainMax ⦋n⦌)) ≫ ·)
    (Iso.inv_hom_id_assoc (SSet.stdSimplex.isoNerve n) _).symm

theorem exUnit_app_app (n : ℕ) (x : X _⦋n⦌) :
    (exUnit.app X).app (Opposite.op ⦋n⦌) x =
      exMk (simplexLastVertex.app ⦋n⦌ ≫ SSet.yonedaEquiv.symm x) := by
  have h := lastVertex.naturality (SSet.yonedaEquiv.symm x)
  simp only [Functor.id_map] at h
  rw [← sdExAdjunction_homEquiv_lastVertex_app, ← sdIso_inv_app_lastVertex_app, Category.assoc,
    ← h]
  have : (SSet.sd : SSet.{u} ⥤ SSet.{u}).IsLeftKanExtension (L := uliftYoneda.{u})
      SSet.stdSimplex.sdIso.inv :=
    inferInstanceAs (SSet.sd.IsLeftKanExtension SSet.stdSimplex.sdIso.inv)
  exact Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} (L := SSet.sd)
    (α := SSet.stdSimplex.sdIso.inv) (lastVertex.app X) x

theorem mem_range_exUnit_iff {n : ℕ} (σ : (SSet.ex.obj X) _⦋n⦌) :
    σ ∈ (SSet.Subcomplex.range (exUnit.app X)).obj (Opposite.op ⦋n⦌) ↔
      σ ∈ fixedSimplices X n 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    change act _ _ = _
    rw [exUnit_app_app]
    change exMk (sdHom (jMap n 0) ≫ simplexLastVertex.app ⦋n⦌ ≫ _) = _
    exact congrArg exMk ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (sdHom_jMap_zero_comp_simplexLastVertex n)))
  · intro hσ
    change act σ _ = σ at hσ
    refine ⟨SSet.yonedaEquiv ((SSet.stdSimplex.isoNerve n).hom ≫
      PartOrd.nerveFunctor.map (PartOrd.ofHom (chainIic ⦋n⦌)) ≫ exHom σ), ?_⟩
    change (exUnit.app X).app (Opposite.op ⦋n⦌) _ = σ
    rw [exUnit_app_app, Equiv.symm_apply_apply]
    conv_rhs => rw [← hσ]
    exact congrArg exMk (sdHom_jMap_zero_comp (exHom σ)).symm

theorem nonDegenerate_of_existsUnique_δ {Y : SSet.{u}} {n : ℕ} {x : Y _⦋n⦌} {y : Y _⦋n + 1⦌}
    (hx : x ∈ Y.nonDegenerate n) (h : ∃! i : Fin (n + 2), Y.δ i y = x) :
    y ∈ Y.nonDegenerate (n + 1) := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate, SSet.degenerate_eq_iUnion_range_σ]
  simp only [Set.mem_iUnion, Set.mem_range, not_exists]
  intro j z hz
  obtain ⟨i, hi, hu⟩ := h
  have key (l : Fin (n + 2)) :
      Y.δ l y = Y.map (SimplexCategory.δ l ≫ SimplexCategory.σ j).op z := by
    rw [← hz, op_comp, Functor.map_comp]
    rfl
  have hmono : Mono (SimplexCategory.δ i ≫ SimplexCategory.σ j) :=
    Y.mono_of_nonDegenerate ⟨x, hx⟩ _ z (by rw [← key, hi])
  have hxz : x = z := by
    rw [← hi, key, SimplexCategory.eq_id_of_mono (SimplexCategory.δ i ≫ SimplexCategory.σ j),
      op_id, CategoryTheory.Functor.map_id]
    rfl
  have h1 := hu j.castSucc (by
    change Y.δ j.castSucc y = x
    rw [key, SimplexCategory.δ_comp_σ_self, op_id, CategoryTheory.Functor.map_id, hxz]
    rfl)
  have h2 := hu j.succ (by
    change Y.δ j.succ y = x
    rw [key, SimplexCategory.δ_comp_σ_succ, op_id, CategoryTheory.Functor.map_id, hxz]
    rfl)
  exact (Fin.castSucc_lt_succ (i := j)).ne (h1.trans h2.symm)

def IsRForm {n : ℕ} (ρ : (SSet.ex.obj X) _⦋n + 1⦌) : Prop :=
  ∃ (h : ℕ) (hh : h ≤ n) (τ : (SSet.ex.obj X) _⦋n⦌), 1 ≤ h ∧ τ ∈ fixedSimplices X n h ∧
    τ ∉ fixedSimplices X n (h - 1) ∧ ρ = act τ (rMap n h hh)

def NotRForm : (n : ℕ) → (SSet.ex.obj X) _⦋n⦌ → Prop
  | 0, _ => True
  | _ + 1, σ => ¬ IsRForm σ

theorem δ_act_rMap_of_lt {m k : ℕ} (hk : k ≤ m + 1) (hk1 : 1 ≤ k)
    {σ : (SSet.ex.obj X) _⦋m + 1⦌} (hσ : σ ∈ fixedSimplices X (m + 1) k) (i : Fin (m + 3))
    (hi : k + 2 ≤ i.val) :
    (SSet.ex.obj X).δ i (act σ (rMap (m + 1) k hk)) ∈ (SSet.ex.obj X).degenerate (m + 1) ∨
      IsRForm ((SSet.ex.obj X).δ i (act σ (rMap (m + 1) k hk))) := by
  have hkm : k ≤ m := by omega
  rw [δ_eq_act, act_rMap_sdCoface_eq hkm hi]
  have hτ : act σ (sdCoface m (i.val - 1)) ∈ fixedSimplices X m k := act_sdCoface_mem_fixedSimplices
      hσ
  by_cases hτ' : act σ (sdCoface m (i.val - 1)) ∈ fixedSimplices X m (k - 1)
  · left
    rw [act_rMap_eq_σ hkm hk1 hτ']
    exact SSet.σ_mem_degenerate _ _ _
  · exact Or.inr ⟨k, hkm, _, hk1, hτ, hτ', rfl⟩

theorem δ_act_rMap_eq_iff {n k : ℕ} (hk : k ≤ n) (hk1 : 1 ≤ k) {σ : (SSet.ex.obj X) _⦋n⦌}
    (hσ : σ ∈ fixedSimplices X n k) (hσ' : σ ∉ fixedSimplices X n (k - 1)) (hnd : σ ∈ (SSet.ex.obj
        X).nonDegenerate n)
    (hR : NotRForm n σ) (i : Fin (n + 2)) :
    (SSet.ex.obj X).δ i (act σ (rMap n k hk)) = σ ↔ i.val = k + 1 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hσ'
      rw [← h, δ_eq_act]
      exact act_rMap_sdCoface_mem_fixedSimplices hk hk1 (by omega) hσ
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases δ_act_rMap_of_lt hk hk1 hσ i (by omega) with hdeg | hR'
      · rw [h] at hdeg
        exact hnd hdeg
      · rw [h] at hR'
        exact hR hR'
  · intro h
    rw [show i = ⟨k + 1, by omega⟩ from Fin.ext h]
    exact δ_act_rMap hk σ

theorem act_rMap_mem_nonDegenerate {n k : ℕ} (hk : k ≤ n) (hk1 : 1 ≤ k)
    {σ : (SSet.ex.obj X) _⦋n⦌} (hσ : σ ∈ fixedSimplices X n k) (hσ' : σ ∉ fixedSimplices X n (k -
        1))
    (hnd : σ ∈ (SSet.ex.obj X).nonDegenerate n) (hR : NotRForm n σ) :
    act σ (rMap n k hk) ∈ (SSet.ex.obj X).nonDegenerate (n + 1) :=
  nonDegenerate_of_existsUnique_δ hnd ⟨⟨k + 1, by omega⟩, δ_act_rMap hk σ,
    fun i hi ↦ Fin.ext ((δ_act_rMap_eq_iff hk hk1 hσ hσ' hnd hR i).1 hi)⟩

theorem act_rMap_notMem_fixedSimplices_zero {n k : ℕ} (hk : k ≤ n) {σ : (SSet.ex.obj X) _⦋n⦌}
    (hσ' : σ ∉ fixedSimplices X n (k - 1)) : act σ (rMap n k hk) ∉ fixedSimplices X (n + 1) 0 := by
  intro h
  apply hσ'
  apply fixedSimplices_mono (Nat.zero_le _)
  rw [← δ_act_rMap hk σ, δ_eq_act]
  exact act_sdCoface_mem_fixedSimplices h

theorem eq_of_mem_fixedSimplices {n k₁ k₂ : ℕ} {σ : (SSet.ex.obj X) _⦋n⦌} (h₁ : σ ∈ fixedSimplices X
    n k₁)
    (h₁' : σ ∉ fixedSimplices X n (k₁ - 1)) (h₂ : σ ∈ fixedSimplices X n k₂) (h₂' : σ ∉
        fixedSimplices X n (k₂ - 1)) : k₁ = k₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h₂' (fixedSimplices_mono (by omega) h₁)
  · exact h₁' (fixedSimplices_mono (by omega) h₂)

theorem exists_mem_fixedSimplices {n : ℕ} (σ : (SSet.ex.obj X) _⦋n⦌) (h0 : σ ∉ fixedSimplices X n 0)
    :
    ∃ k, k ≤ n ∧ 1 ≤ k ∧ σ ∈ fixedSimplices X n k ∧ σ ∉ fixedSimplices X n (k - 1) := by
  classical
  have hex : ∃ k, σ ∈ fixedSimplices X n k := ⟨n, mem_fixedSimplices_of_le le_rfl σ⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (mem_fixedSimplices_of_le le_rfl σ), ?_, Nat.find_spec
      hex, ?_⟩
  · by_contra h
    exact h0 (by simpa [show Nat.find hex = 0 by omega] using Nat.find_spec hex)
  · intro h
    have h' : Nat.find hex ≠ 0 := fun h' ↦ h0 (by simpa [h'] using Nat.find_spec hex)
    exact Nat.find_min hex (by omega) h

theorem le_of_act_rMap_eq {n k₁ k₂ : ℕ} (hk₁ : k₁ ≤ n) (hk₂ : k₂ ≤ n)
    {σ₁ σ₂ : (SSet.ex.obj X) _⦋n⦌} (hσ₁ : σ₁ ∈ fixedSimplices X n k₁) (hσ₂' : σ₂ ∉ fixedSimplices X
        n (k₂ - 1))
    (h : act σ₁ (rMap n k₁ hk₁) = act σ₂ (rMap n k₂ hk₂)) : k₂ ≤ k₁ := by
  have hρ : act σ₁ (rMap n k₁ hk₁) ∈ fixedSimplices X (n + 1) k₁ := act_rMap_mem_fixedSimplices hk₁
      le_rfl hσ₁
  have hσ₂ : σ₂ ∈ fixedSimplices X n k₁ := by
    rw [← δ_act_rMap hk₂ σ₂, ← h, δ_eq_act]
    exact act_sdCoface_mem_fixedSimplices hρ
  by_contra hlt
  exact hσ₂' (fixedSimplices_mono (by omega) hσ₂)

theorem eq_of_act_rMap_eq {n k₁ k₂ : ℕ} (hk₁ : k₁ ≤ n) (hk₂ : k₂ ≤ n)
    {σ₁ σ₂ : (SSet.ex.obj X) _⦋n⦌} (hσ₁ : σ₁ ∈ fixedSimplices X n k₁) (hσ₁' : σ₁ ∉ fixedSimplices X
        n (k₁ - 1))
    (hσ₂ : σ₂ ∈ fixedSimplices X n k₂) (hσ₂' : σ₂ ∉ fixedSimplices X n (k₂ - 1))
    (h : act σ₁ (rMap n k₁ hk₁) = act σ₂ (rMap n k₂ hk₂)) : k₁ = k₂ ∧ σ₁ = σ₂ := by
  obtain rfl : k₁ = k₂ :=
    le_antisymm (le_of_act_rMap_eq hk₂ hk₁ hσ₂ hσ₁' h.symm) (le_of_act_rMap_eq hk₁ hk₂ hσ₁ hσ₂' h)
  refine ⟨rfl, ?_⟩
  rw [← δ_act_rMap hk₁ σ₁, h, δ_act_rMap]

theorem typeII_of_act_rMap {m h : ℕ} (hh : h ≤ m) (h1 : 1 ≤ h) {τ : (SSet.ex.obj X) _⦋m⦌}
    (hτ : τ ∈ fixedSimplices X m h) (hτ' : τ ∉ fixedSimplices X m (h - 1))
    (hρ : act τ (rMap m h hh) ∈ (SSet.ex.obj X).nonDegenerate (m + 1)) :
    τ ∈ (SSet.ex.obj X).nonDegenerate m ∧ NotRForm m τ := by
  constructor
  · intro hdeg
    cases m with
    | zero => simp at hdeg
    | succ m =>
      rw [SSet.degenerate_eq_iUnion_range_σ] at hdeg
      simp only [Set.mem_iUnion, Set.mem_range] at hdeg
      obtain ⟨j, τ₀, rfl⟩ := hdeg
      exact hρ (act_rMap_mem_degenerate hh j τ₀ hτ)
  · cases m with
    | zero => trivial
    | succ m =>
      rintro ⟨h', hh', τ', h1', hτ'₁, hτ'₂, rfl⟩
      have hτ'h : τ' ∈ fixedSimplices X m h := by
        rw [← δ_act_rMap hh' τ', δ_eq_act]
        exact act_sdCoface_mem_fixedSimplices hτ
      have hτh' : act τ' (rMap m h' hh') ∈ fixedSimplices X (m + 1) h' :=
          act_rMap_mem_fixedSimplices hh' le_rfl hτ'₁
      obtain rfl : h' = h := by
        refine le_antisymm ?_ ?_
        · by_contra hlt
          exact hτ'₂ (fixedSimplices_mono (by omega) hτ'h)
        · by_contra hlt
          exact hτ' (fixedSimplices_mono (by omega) hτh')
      apply hρ
      rw [act_rMap_rMap_eq_σ hh' hτ'₁]
      exact SSet.σ_mem_degenerate _ _ _

variable (X) in
structure TypeIISimplex where
  n : ℕ
  σ : (SSet.ex.obj X) _⦋n⦌
  k : ℕ
  hk : k ≤ n
  one_le : 1 ≤ k
  mem : σ ∈ fixedSimplices X n k
  notMem : σ ∉ fixedSimplices X n (k - 1)
  nonDeg : σ ∈ (SSet.ex.obj X).nonDegenerate n
  notR : NotRForm n σ

theorem TypeIISimplex.eq_of_sMk_eq {s t : TypeIISimplex X} (h : SSet.S.mk s.σ = SSet.S.mk t.σ) : s =
    t := by
  obtain ⟨n, σ, k, hk, h1, hm, hn, hd, hr⟩ := s
  obtain ⟨n', σ', k', hk', h1', hm', hn', hd', hr'⟩ := t
  obtain rfl : n = n' := SSet.S.dim_eq_of_mk_eq h
  obtain rfl : σ = σ' := (SSet.S.ext_iff _ _).1 h
  obtain rfl : k = k' := eq_of_mem_fixedSimplices hm hn hm' hn'
  rfl

variable (X) in
noncomputable def pairingCore : (SSet.Subcomplex.range (exUnit.app X)).PairingCore where
  ι := TypeIISimplex X
  dim s := s.n
  simplex s := act s.σ (rMap s.n s.k s.hk)
  index s := ⟨s.k + 1, by have := s.hk; omega⟩
  nonDegenerate₁ s := act_rMap_mem_nonDegenerate s.hk s.one_le s.mem s.notMem s.nonDeg s.notR
  nonDegenerate₂ s := by
    rw [δ_act_rMap]
    exact s.nonDeg
  notMem₁ s := by
    rw [mem_range_exUnit_iff]
    exact act_rMap_notMem_fixedSimplices_zero s.hk s.notMem
  notMem₂ s := by
    rw [δ_act_rMap, mem_range_exUnit_iff]
    exact fun h ↦ s.notMem (fixedSimplices_mono (Nat.zero_le _) h)
  injective_type₁' {s t} h := by
    obtain ⟨n, σ, k, hk, h1, hm, hn, hd, hr⟩ := s
    obtain ⟨n', σ', k', hk', h1', hm', hn', hd', hr'⟩ := t
    obtain rfl : n = n' := Nat.succ.inj (SSet.S.dim_eq_of_mk_eq h)
    obtain ⟨rfl, rfl⟩ := eq_of_act_rMap_eq hk hk' hm hn hm' hn' ((SSet.S.ext_iff _ _).1 h)
    rfl
  injective_type₂' {s t} h := by
    rw [δ_act_rMap, δ_act_rMap] at h
    exact TypeIISimplex.eq_of_sMk_eq h
  type₁_ne_type₂' s t h := by
    rw [δ_act_rMap] at h
    obtain ⟨n, σ, k, hk, h1, hm, hn, hd, hr⟩ := s
    obtain ⟨n', σ', k', hk', h1', hm', hn', hd', hr'⟩ := t
    obtain rfl : n + 1 = n' := SSet.S.dim_eq_of_mk_eq h
    exact hr' ⟨k, hk, σ, h1, hm, hn, ((SSet.S.ext_iff _ _).1 h).symm⟩
  surjective' x := by
    obtain ⟨d, y, hy, hy', rfl⟩ := SSet.Subcomplex.N.mk_surjective x
    have hy0 : y ∉ fixedSimplices X d 0 := fun h ↦ hy' ((mem_range_exUnit_iff y).2 h)
    by_cases hR : NotRForm d y
    · obtain ⟨k, hkd, hk1, hmem, hnot⟩ := exists_mem_fixedSimplices y hy0
      refine ⟨⟨d, y, k, hkd, hk1, hmem, hnot, hy, hR⟩, Or.inr ?_⟩
      change SSet.S.mk y = SSet.S.mk ((SSet.ex.obj X).δ _ (act y (rMap d k hkd)))
      rw [δ_act_rMap]
    · cases d with
      | zero => exact absurd trivial hR
      | succ m =>
        obtain ⟨h, hh, τ, h1, hτ, hτ', rfl⟩ := not_not.1 hR
        obtain ⟨hτnd, hτR⟩ := typeII_of_act_rMap hh h1 hτ hτ' hy
        exact ⟨⟨m, τ, h, hh, h1, hτ, hτ', hτnd, hτR⟩, Or.inl rfl⟩

instance : (pairingCore X).IsProper where
  isUniquelyCodimOneFace (s : TypeIISimplex X) := by
    refine (SSet.S.IsUniquelyCodimOneFace.iff _ _).2 ?_
    change ∃! i, (SSet.ex.obj X).δ i (act s.σ (rMap s.n s.k s.hk)) =
      (SSet.ex.obj X).δ ⟨s.k + 1, by have := s.hk; omega⟩ (act s.σ (rMap s.n s.k s.hk))
    rw [δ_act_rMap]
    exact ⟨⟨s.k + 1, by have := s.hk; omega⟩, δ_act_rMap s.hk s.σ,
      fun i hi ↦ Fin.ext ((δ_act_rMap_eq_iff s.hk s.one_le s.mem s.notMem s.nonDeg s.notR i).1 hi)⟩

variable (X) in
def weakRankFunction : (pairingCore X).WeakRankFunction ℕ where
  rank s := s.k
  lt {s t} hst hdim := by
    obtain ⟨hne, hlt⟩ := hst
    have hle := hlt.le
    rw [SSet.Subcomplex.N.le_iff, SSet.N.le_iff_exists_mono] at hle
    obtain ⟨f, hf, hft⟩ := hle
    obtain ⟨n, σ, k, hk, h1, hm, hn, hd, hr⟩ := s
    obtain ⟨n', σ', k', hk', h1', hm', hn', hd', hr'⟩ := t
    change n = n' at hdim
    subst hdim
    change k < k'
    obtain ⟨i, rfl⟩ := @SimplexCategory.eq_δ_of_mono n f hf
    change (SSet.ex.obj X).δ i (act σ' (rMap n k' hk')) =
      (SSet.ex.obj X).δ ⟨k + 1, by omega⟩ (act σ (rMap n k hk)) at hft
    rw [δ_act_rMap] at hft
    rcases lt_trichotomy i.val (k' + 1) with hi | hi | hi
    · have hσ : σ ∈ fixedSimplices X n (k' - 1) := by
        rw [← hft, δ_eq_act]
        exact act_rMap_sdCoface_mem_fixedSimplices hk' h1' (by omega) hm'
      by_contra hkk
      exact hn (fixedSimplices_mono (by omega) hσ)
    · rw [(δ_act_rMap_eq_iff hk' h1' hm' hn' hd' hr' i).2 hi] at hft
      subst hft
      exact absurd (TypeIISimplex.eq_of_sMk_eq (by rfl)) hne
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases δ_act_rMap_of_lt hk' h1' hm' i (by omega) with hdeg | hR'
      · rw [hft] at hdeg
        exact absurd hdeg hd
      · rw [hft] at hR'
        exact absurd hR' hr

variable {Y : SSet.{u}}

noncomputable abbrev preimageRangeExUnit (f : X ⟶ Y) : (SSet.ex.obj X).Subcomplex :=
  (SSet.Subcomplex.range (exUnit.app Y)).preimage (SSet.ex.map f)

theorem range_le_preimageRangeExUnit (f : X ⟶ Y) : SSet.Subcomplex.range (exUnit.app X) ≤
    preimageRangeExUnit f := by
  rintro ⟨n⟩ σ hσ
  induction n using SimplexCategory.rec with | _ n
  rw [mem_range_exUnit_iff] at hσ
  change (SSet.ex.map f).app _ σ ∈ (SSet.Subcomplex.range (exUnit.app Y)).obj _
  rw [mem_range_exUnit_iff]
  change act _ _ = _
  rw [← ex_map_act]
  exact congrArg _ hσ

theorem subcomplex_pairing_p_le (f : X ⟶ Y) (x : (pairingCore X).pairing.II)
    (hx : x.1.toS.subcomplex ≤ preimageRangeExUnit f) :
    ((pairingCore X).pairing.p x).1.toS.subcomplex ≤ preimageRangeExUnit f := by
  obtain ⟨s, hs⟩ := x.2
  have key : ((pairingCore X).pairing.p x).1 =
      (pairingCore X).type₁ ((pairingCore X).equivII.symm x) := rfl
  have hs' : (pairingCore X).equivII.symm x = s := (Equiv.symm_apply_eq _).2 (Subtype.ext hs.symm)
  rw [key, hs']
  rw [← hs] at hx
  change SSet.Subcomplex.ofSimplex ((SSet.ex.obj X).δ ⟨s.k + 1, by have := s.hk; omega⟩
    (act s.σ (rMap s.n s.k s.hk))) ≤ preimageRangeExUnit f at hx
  change SSet.Subcomplex.ofSimplex (act s.σ (rMap s.n s.k s.hk)) ≤ preimageRangeExUnit f
  rw [SSet.Subcomplex.ofSimplex_le_iff, δ_act_rMap] at hx
  rw [SSet.Subcomplex.ofSimplex_le_iff]
  change (SSet.ex.map f).app _ s.σ ∈ (SSet.Subcomplex.range (exUnit.app Y)).obj _ at hx
  change (SSet.ex.map f).app _ _ ∈ (SSet.Subcomplex.range (exUnit.app Y)).obj _
  rw [mem_range_exUnit_iff] at hx ⊢
  rw [ex_map_act]
  exact act_rMap_mem_fixedSimplices s.hk (Nat.zero_le _) hx

noncomputable def pullbackIso (f : X ⟶ Y) :
    pullback (exUnit.app Y) (SSet.ex.map f) ≅ (preimageRangeExUnit f : SSet.{u}) where
  hom := SSet.Subcomplex.lift (pullback.snd _ _) (by
    rw [← SSet.Subcomplex.image_le_iff, ← SSet.Subcomplex.range_comp, ← pullback.condition,
      SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _)
  inv := pullback.lift ((SSet.Subcomplex.range (exUnit.app Y)).fromPreimage (SSet.ex.map f) ≫
      inv (SSet.Subcomplex.toRange (exUnit.app Y))) (preimageRangeExUnit f).ι (by
    rw [Category.assoc, Subfunctor.inv_toRange_comp]
    exact SSet.Subcomplex.fromPreimage_ι _ _)
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [← cancel_mono (exUnit.app Y)]
      simp only [Category.assoc, Category.id_comp, pullback.condition, pullback.lift_snd_assoc,
        SSet.Subcomplex.lift_ι_assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      rfl
  inv_hom_id := by
    rw [← cancel_mono (preimageRangeExUnit f).ι, Category.assoc, SSet.Subcomplex.lift_ι,
        pullback.lift_snd,
      Category.id_comp]

theorem exRelativeUnit_comp_pullbackIso (f : X ⟶ Y) :
    exRelativeUnit f ≫ (pullbackIso f).hom =
      SSet.Subcomplex.toRange (exUnit.app X) ≫ SSet.Subcomplex.homOfLE (range_le_preimageRangeExUnit
          f) := by
  rw [← cancel_mono (preimageRangeExUnit f).ι, Category.assoc, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι]
  have h : (pullbackIso f).hom ≫ (preimageRangeExUnit f).ι = pullback.snd _ _ := rfl
  rw [h, exRelativeUnit, pullback.lift_snd]

end MossUnit

open MossUnit in
theorem strongAnodyneExtensions_exUnit_app (X : SSet.{u}) :
    SSet.strongAnodyneExtensions (exUnit.app X) := by
  have := (weakRankFunction X).isRegular
  exact ⟨inferInstance, (pairingCore X).pairing, inferInstance⟩

open MossUnit in
theorem strongAnodyneExtensions_exRelativeUnit {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.strongAnodyneExtensions (exRelativeUnit f) := by
  have := (weakRankFunction X).isRegular
  refine (MorphismProperty.cancel_right_of_respectsIso SSet.strongAnodyneExtensions _
    (pullbackIso f).hom).1 ?_
  rw [exRelativeUnit_comp_pullbackIso]
  exact (MorphismProperty.cancel_left_of_respectsIso SSet.strongAnodyneExtensions _ _).2
    (strongAnodyneExtensions_homOfLE_of_pairing (range_le_preimageRangeExUnit f) (pairingCore
        X).pairing
      (subcomplex_pairing_p_le f))

end Atoms.Homotopical
