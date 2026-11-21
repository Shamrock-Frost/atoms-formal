import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite

universe u

namespace SSet

class Isofibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop extends InnerFibration p where
  exists_lift (x₀ : X _⦋0⦌) {y₁ : Y _⦋0⦌} (g : Edge (p.app _ x₀) y₁)
    (hg : Nonempty g.InvStruct) :
    ∃ (x₁ : X _⦋0⦌) (f : Edge x₀ x₁), Nonempty f.InvStruct ∧ (f.map p).edge = g.edge

instance isofibration_terminal_from (X : SSet.{u}) [X.Quasicategory] :
    Isofibration (terminal.from X) where
  exists_lift x₀ _ _ _ :=
    ⟨x₀, Edge.id x₀, ⟨Edge.InvStruct.invStructId x₀⟩,
      yonedaEquiv.symm.injective (terminal.hom_ext _ _)⟩

section Core

def core (X : SSet.{u}) : X.Subcomplex where
  obj n := {σ | ∀ f : ⦋1⦌ ⟶ n.unop,
    IsIso (Truncated.HomotopyCategory.homMk (Edge.mk' (X.map f.op σ)))}
  map {n m} θ σ hσ f := by
    have := hσ (f ≫ θ.unop)
    rwa [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] at this

private lemma isIso_homMk_iff_of_edge_eq {X : SSet.{u}} {x y x' y' : X _⦋0⦌} (e : Edge x y)
    (e' : Edge x' y') (h : e.edge = e'.edge) :
    IsIso (Truncated.HomotopyCategory.homMk e) ↔ IsIso (Truncated.HomotopyCategory.homMk e') := by
  obtain rfl : x = x' := e.src_eq.symm.trans ((congrArg _ h).trans e'.src_eq)
  obtain rfl : y = y' := e.tgt_eq.symm.trans ((congrArg _ h).trans e'.tgt_eq)
  obtain rfl : e = e' := Edge.ext h
  rfl

lemma isIso_homMk_of_mem_core {X : SSet.{u}} {x y : X _⦋0⦌} (e : Edge x y)
    (he : e.edge ∈ X.core.obj _) : IsIso (Truncated.HomotopyCategory.homMk e) := by
  have := he (𝟙 _)
  rwa [op_id, Functor.map_id_apply,
    isIso_homMk_iff_of_edge_eq _ e (Edge.mk'_edge _)] at this

private lemma map_comp_op_apply {X : SSet.{u}} {a b c : SimplexCategory} (g₁ : a ⟶ b)
    (g₂ : b ⟶ c) (σ : X.obj (op c)) : X.map (g₁ ≫ g₂).op σ = X.map g₁.op (X.map g₂.op σ) := by
  rw [op_comp, Functor.map_comp_apply]

private lemma simplexCategory_hom_ext {m n : ℕ} {f g : ⦋m⦌ ⟶ ⦋n⦌}
    (h : ∀ i, f.toOrderHom i = g.toOrderHom i) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext h))

theorem mem_core_of_isIso {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌)
    (h : ∀ i : Fin (n + 1), 0 < i → IsIso (Truncated.HomotopyCategory.homMk
      (Edge.mk' (X.map (SimplexCategory.mkOfLe 0 i (Fin.zero_le _)).op σ)))) :
    σ ∈ X.core.obj _ := by
  intro f
  let v (i : Fin (n + 1)) : X _⦋0⦌ := X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ
  have hδ (k : Fin 2) (g : ⦋1⦌ ⟶ ⦋n⦌) (i : Fin (n + 1))
      (hg : SimplexCategory.δ k ≫ g = SimplexCategory.const ⦋0⦌ ⦋n⦌ i) :
      X.δ k (X.map g.op σ) = v i := by
    rw [SimplicialObject.δ_def, ← Functor.map_comp_apply, ← op_comp, hg]
  let e (i j : Fin (n + 1)) (hij : i ≤ j) : Edge (v i) (v j) :=
    Edge.mk (X.map (SimplexCategory.mkOfLe i j hij).op σ)
      (hδ 1 _ _ (simplexCategory_hom_ext fun k ↦ by fin_cases k; rfl))
      (hδ 0 _ _ (simplexCategory_hom_ext fun k ↦ by fin_cases k; rfl))
  have he (i : Fin (n + 1)) : IsIso (Truncated.HomotopyCategory.homMk (e 0 i (Fin.zero_le _))) := by
    obtain rfl | hi := (Fin.zero_le i).eq_or_lt
    · rw [isIso_homMk_iff_of_edge_eq _ (Edge.id (v 0))]
      · exact (Edge.InvStruct.invStructId (v 0)).isIso_homMk
      · exact (congrArg (fun g ↦ X.map (Quiver.Hom.op g) σ)
          (simplexCategory_hom_ext (g := SimplexCategory.σ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
            fun k ↦ by fin_cases k <;> rfl)).trans (map_comp_op_apply _ _ σ)
    · exact (isIso_homMk_iff_of_edge_eq (e 0 i _) (Edge.mk' _) rfl).2 (h i hi)
  have hf : f = SimplexCategory.mkOfLe (f.toOrderHom 0) (f.toOrderHom 1)
      (f.toOrderHom.monotone (Fin.zero_le _)) :=
    simplexCategory_hom_ext fun k ↦ by fin_cases k <;> rfl
  rw [hf, isIso_homMk_iff_of_edge_eq (Edge.mk' _)
    (e _ _ (f.toOrderHom.monotone (Fin.zero_le _))) rfl]
  let τ := X.map (SimplexCategory.mkOfLeComp 0 (f.toOrderHom 0) (f.toOrderHom 1) (Fin.zero_le _)
    (f.toOrderHom.monotone (Fin.zero_le _))).op σ
  have hτ (k : Fin 3) (g : ⦋1⦌ ⟶ ⦋n⦌)
      (hg : SimplexCategory.δ k ≫ SimplexCategory.mkOfLeComp 0 (f.toOrderHom 0) (f.toOrderHom 1)
        (Fin.zero_le _) (f.toOrderHom.monotone (Fin.zero_le _)) = g) :
      X.δ k τ = X.map g.op σ := by
    rw [SimplicialObject.δ_def, ← Functor.map_comp_apply, ← op_comp, hg]
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk
    (Edge.CompStruct.mk (e₀₁ := e 0 (f.toOrderHom 0) (Fin.zero_le _))
      (e₁₂ := e (f.toOrderHom 0) (f.toOrderHom 1) (f.toOrderHom.monotone (Fin.zero_le _)))
      (e₀₂ := e 0 (f.toOrderHom 1) (Fin.zero_le _)) τ
      (hτ 2 _ (simplexCategory_hom_ext fun k ↦ by fin_cases k <;> rfl))
      (hτ 0 _ (simplexCategory_hom_ext fun k ↦ by fin_cases k <;> rfl))
      (hτ 1 _ (simplexCategory_hom_ext fun k ↦ by fin_cases k <;> rfl)))
  have : IsIso (Truncated.HomotopyCategory.homMk (e 0 _ (Fin.zero_le _)).toTruncated) :=
    he (f.toOrderHom 0)
  have : IsIso (Truncated.HomotopyCategory.homMk (e 0 _ (Fin.zero_le _)).toTruncated ≫
      Truncated.HomotopyCategory.homMk (e (f.toOrderHom 0) (f.toOrderHom 1)
        (f.toOrderHom.monotone (Fin.zero_le _))).toTruncated) := by
    rw [hc]
    exact he (f.toOrderHom 1)
  exact IsIso.of_isIso_comp_left
    (Truncated.HomotopyCategory.homMk (e 0 (f.toOrderHom 0) (Fin.zero_le _)).toTruncated)
    (Truncated.HomotopyCategory.homMk (e (f.toOrderHom 0) (f.toOrderHom 1)
      (f.toOrderHom.monotone (Fin.zero_le _))).toTruncated)

theorem edge_mem_core_of_isIso {X : SSet.{u}} {x y : X _⦋0⦌} (e : Edge x y)
    (he : IsIso (Truncated.HomotopyCategory.homMk e)) : e.edge ∈ X.core.obj _ := by
  refine mem_core_of_isIso _ fun i hi ↦ ?_
  obtain rfl : i = 1 := by
    fin_cases i
    · exact absurd hi (lt_irrefl _)
    · rfl
  rw [show SimplexCategory.mkOfLe (0 : Fin 2) 1 (Fin.zero_le _) = 𝟙 _ from
    simplexCategory_hom_ext fun k ↦ by fin_cases k <;> rfl, op_id, Functor.map_id_apply]
  exact (isIso_homMk_iff_of_edge_eq e (Edge.mk' e.edge) rfl).1 he

theorem mem_core_of_δ_mem_core {X : SSet.{u}} (σ : X _⦋2⦌) (k : Fin 3)
    (h : ∀ j, j ≠ k → X.δ j σ ∈ X.core.obj _) : σ ∈ X.core.obj _ := by
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, c, rfl⟩ := Edge.CompStruct.exists_of_simplex σ
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk c
  have hi (j : Fin 3) (hj : j ≠ k) {y y' : X _⦋0⦌} (e : Edge y y') (he : X.δ j c.simplex = e.edge) :
      IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) :=
    isIso_homMk_of_mem_core e (he ▸ h j hj)
  have h₀₁ : IsIso (Truncated.HomotopyCategory.homMk e₀₁.toTruncated) ∧
      IsIso (Truncated.HomotopyCategory.homMk e₀₂.toTruncated) := by
    fin_cases k
    · exact ⟨hi 2 (by decide) e₀₁ c.d₂, hi 1 (by decide) e₀₂ c.d₁⟩
    · have h₀₁ := hi 2 (by decide) e₀₁ c.d₂
      have h₁₂ := hi 0 (by decide) e₁₂ c.d₀
      refine ⟨h₀₁, ?_⟩
      rw [← hc]
      infer_instance
    · have h₁₂ := hi 0 (by decide) e₁₂ c.d₀
      have h₀₂ := hi 1 (by decide) e₀₂ c.d₁
      have : IsIso (Truncated.HomotopyCategory.homMk e₀₁.toTruncated ≫
          Truncated.HomotopyCategory.homMk e₁₂.toTruncated) := by
        rw [hc]
        exact h₀₂
      exact ⟨IsIso.of_isIso_comp_right _ (Truncated.HomotopyCategory.homMk e₁₂.toTruncated), h₀₂⟩
  refine mem_core_of_isIso _ fun i hi ↦ ?_
  fin_cases i
  · exact absurd hi (lt_irrefl _)
  · refine (isIso_homMk_iff_of_edge_eq _ e₀₁ ?_).2 h₀₁.1
    exact (congrArg (fun g ↦ X.map (Quiver.Hom.op g) c.simplex)
      (simplexCategory_hom_ext (g := SimplexCategory.δ 2) fun k ↦ by fin_cases k <;> rfl)).trans
        c.d₂
  · refine (isIso_homMk_iff_of_edge_eq _ e₀₂ ?_).2 h₀₁.2
    exact (congrArg (fun g ↦ X.map (Quiver.Hom.op g) c.simplex)
      (simplexCategory_hom_ext (g := SimplexCategory.δ 1) fun k ↦ by fin_cases k <;> rfl)).trans
        c.d₁

theorem mem_core_of_horn {X : SSet.{u}} {n : ℕ} {k : Fin (n + 3)} (σ : Δ[n + 2] ⟶ X)
    (a : (Λ[n + 2, k] : SSet.{u}) ⟶ X.core) (h : Λ[n + 2, k].ι ≫ σ = a ≫ X.core.ι) :
    yonedaEquiv σ ∈ X.core.obj _ := by
  cases n with
  | zero =>
    refine mem_core_of_δ_mem_core _ k fun j hj ↦ ?_
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc k j hj, h, yonedaEquiv_comp]
    exact (a.app _ _).2
  | succ m =>
    refine mem_core_of_isIso _ fun i hi ↦ ?_
    have hcard : ({k, 0, i} : Finset (Fin (m + 1 + 2 + 1))).card ≤ m + 1 + 2 :=
      Finset.card_le_three.trans (by omega)
    have he : X.map (SimplexCategory.mkOfLe 0 i (Fin.zero_le _)).op (yonedaEquiv σ) =
        (a ≫ X.core.ι).app _ (horn.edge (m + 1 + 2) k 0 i (Fin.zero_le _) hcard) := by
      rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_map]
      exact (congrArg (σ.app _) (stdSimplex.ext _ _ fun k ↦ by fin_cases k <;> rfl)).trans
        (congrArg (fun φ ↦ φ.app _ (horn.edge (m + 1 + 2) k 0 i (Fin.zero_le _) hcard)) h)
    rw [isIso_homMk_iff_of_edge_eq (Edge.mk' (X.map (SimplexCategory.mkOfLe 0 i
      (Fin.zero_le _)).op (yonedaEquiv σ))) (Edge.mk' ((a ≫ X.core.ι).app _
      (horn.edge (m + 1 + 2) k 0 i (Fin.zero_le _) hcard))) he]
    exact isIso_homMk_of_mem_core _ (a.app _ _).2

theorem range_le_core {K X : SSet.{u}} (g : K ⟶ X)
    (hK : ∀ e : K _⦋1⦌, Nonempty (Edge.mk' e).InvStruct) : Subcomplex.range g ≤ X.core := by
  rintro n _ ⟨σ, rfl⟩ f
  rw [isIso_homMk_iff_of_edge_eq _ ((Edge.mk' (K.map f.op σ)).map g)
    (NatTrans.naturality_apply g f.op σ).symm]
  exact (hK _).some.map g |>.isIso_homMk

theorem range_core_ι_comp_le_core {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    Subcomplex.range (X.core.ι ≫ p) ≤ Y.core := by
  rintro n _ ⟨⟨σ, hσ⟩, rfl⟩ f
  rw [isIso_homMk_iff_of_edge_eq _ ((Edge.mk' (X.map f.op σ)).map p)
    (NatTrans.naturality_apply p f.op σ).symm]
  exact ((isIso_homMk_iff _).1 (hσ f)).some.map p |>.isIso_homMk

def coreMap {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    (X.core : SSet.{u}) ⟶ (Y.core : SSet.{u}) :=
  Subcomplex.lift (X.core.ι ≫ p) (range_core_ι_comp_le_core p)

lemma coreMap_ι {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    coreMap p ≫ Y.core.ι = X.core.ι ≫ p :=
  Subcomplex.lift_ι _ _

theorem hasLiftingProperty_horn_coreMap_of_hasLift {X Y : SSet.{u}} [X.Quasicategory]
    (p : X ⟶ Y) {n : ℕ} (k : Fin (n + 3))
    (h : ∀ (a : (Λ[n + 2, k] : SSet.{u}) ⟶ X.core) (b : Δ[n + 2] ⟶ Y.core)
      (sq : CommSq (a ≫ X.core.ι) Λ[n + 2, k].ι p (b ≫ Y.core.ι)), sq.HasLift) :
    HasLiftingProperty Λ[n + 2, k].ι (coreMap p) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨l⟩ := (h a b ⟨by
    rw [Category.assoc, ← coreMap_ι, ← Category.assoc, sq.w, Category.assoc]⟩).exists_lift
  have hr : Subcomplex.range l.l ≤ X.core := by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
    exact mem_core_of_horn l.l a l.fac_left
  refine ⟨⟨⟨Subcomplex.lift l.l hr, ?_, ?_⟩⟩⟩
  · rw [← cancel_mono X.core.ι, Category.assoc, Subcomplex.lift_ι, l.fac_left]
  · rw [← cancel_mono Y.core.ι]
    simp only [Category.assoc, coreMap_ι, Subcomplex.lift_ι_assoc, l.fac_right]

lemma hasLiftingProperty_horn_zero_coreMap {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Isofibration p] (n : ℕ) :
    HasLiftingProperty Λ[n + 1, 0].ι (coreMap p) := by
  cases n with
  | zero =>
    refine ⟨fun {u v} sq ↦ ?_⟩
    have hw : (u ≫ X.core.ι) ≫ p = Λ[0 + 1, 0].ι ≫ v ≫ Y.core.ι := by
      rw [Category.assoc, ← coreMap_ι, ← Category.assoc, sq.w, Category.assoc]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hx : p.app _ (yonedaEquiv (horn.ι 0 1 h10 ≫ u ≫ X.core.ι)) =
        Y.δ 1 (yonedaEquiv (v ≫ Y.core.ι)) := by
      rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, ← Category.assoc u, hw,
        horn.ι_ι_assoc, stdSimplex.yonedaEquiv_δ_comp]
    obtain ⟨x₁, f, ⟨I⟩, hf⟩ := Isofibration.exists_lift _
      (Edge.mk (yonedaEquiv (v ≫ Y.core.ι)) hx.symm rfl)
      ((isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ (yonedaEquiv v).2))
    have hr : Subcomplex.range (yonedaEquiv.symm f.edge) ≤ X.core := by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, Equiv.apply_symm_apply]
      exact edge_mem_core_of_isIso f I.isIso_homMk
    refine ⟨⟨⟨Subcomplex.lift _ hr, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono X.core.ι, Category.assoc, Subcomplex.lift_ι]
      refine horn.hom_ext' fun j hj ↦ ?_
      obtain rfl : j = 1 := by
        fin_cases j
        · exact (hj rfl).elim
        · rfl
      rw [horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, f.src_eq, Equiv.symm_apply_apply]
    · rw [← cancel_mono Y.core.ι, Category.assoc, coreMap_ι, Subcomplex.lift_ι_assoc]
      refine yonedaEquiv.injective ?_
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hf]
      rfl
  | succ m =>
    exact hasLiftingProperty_horn_coreMap_of_hasLift p 0 fun a _ sq ↦
      hasLift_horn_zero_of_invStruct p sq
        ((isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ (a.app _ _).2))

end Core

section Pairing

private lemma hasLiftingProperty_ι_of_pairingCore {Z : SSet.{u}} {A : Z.Subcomplex}
    (h : A.PairingCore) [h.IsRegular] {E B : SSet.{u}} (q : E ⟶ B)
    (hq : ∀ s : h.ι, HasLiftingProperty (horn (h.dim s + 1) (h.index s)).ι q) :
    HasLiftingProperty A.ι q := by
  have hII (x : h.pairing.II) : HasLiftingProperty
      (horn (x.1.dim + 1) ((h.pairing.isUniquelyCodimOneFace x).index rfl)).ι q := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rw [Subcomplex.PairingCore.pairing_isUniquelyCodimOneFace_index]
    exact hq s
  rw [← llp_ofHoms_iff_hasLiftingProperty Unit]
  exact transfiniteCompositionsOfShape_le _ _ _
    ⟨h.pairing.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _) _
        (h.pairing.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      rw [llp_ofHoms_iff_hasLiftingProperty]
      exact hII c.s⟩

end Pairing

namespace coherentIso

def simplexEquiv {d : ℕ} : coherentIso.{u} _⦋d⦌ ≃ (Fin (d + 1) → Bool) :=
  Codiscrete.equivFun.trans (Equiv.arrowCongr (Equiv.refl _) Equiv.ulift)

private lemma simplexEquiv_δ {d : ℕ} (i : Fin (d + 2)) (x : coherentIso.{u} _⦋d + 1⦌) :
    simplexEquiv (coherentIso.δ i x) = simplexEquiv x ∘ i.succAbove :=
  rfl

private lemma simplexEquiv_σ {d : ℕ} (i : Fin (d + 1)) (x : coherentIso.{u} _⦋d⦌) :
    simplexEquiv (coherentIso.σ i x) = simplexEquiv x ∘ i.predAbove :=
  rfl

private lemma mem_nonDegenerate_iff {d : ℕ} (x : coherentIso.{u} _⦋d⦌) :
    x ∈ coherentIso.nonDegenerate d ↔
      ∀ i : Fin d, simplexEquiv x i.castSucc ≠ simplexEquiv x i.succ := by
  cases d with
  | zero => simp [nondegenerate_zero]
  | succ d =>
    rw [← not_iff_not, ← mem_degenerate_iff_notMem_nonDegenerate, degenerate_eq_iUnion_range_σ,
      Set.mem_iUnion]
    push Not
    refine exists_congr fun i ↦ ⟨?_, fun h ↦ ⟨coherentIso.δ i.castSucc x,
      simplexEquiv.injective (funext fun j ↦ ?_)⟩⟩
    · rintro ⟨y, rfl⟩
      simp [simplexEquiv_σ]
    · rw [simplexEquiv_σ, simplexEquiv_δ]
      by_cases hj : j = i.castSucc
      · subst hj
        simp [h]
      · simp [Fin.succAbove_predAbove hj]

private def alt (b : Bool) (d : ℕ) : coherentIso.{u} _⦋d⦌ :=
  simplexEquiv.symm fun i ↦ if i.val % 2 = 0 then b else !b

private lemma simplexEquiv_alt (b : Bool) (d : ℕ) (i : Fin (d + 1)) :
    simplexEquiv (alt.{u} b d) i = if i.val % 2 = 0 then b else !b := by
  simp [alt]

private lemma simplexEquiv_alt_zero (b : Bool) (d : ℕ) : simplexEquiv (alt.{u} b d) 0 = b := by
  simp [simplexEquiv_alt]

private lemma alt_mem_nonDegenerate (b : Bool) (d : ℕ) :
    alt.{u} b d ∈ coherentIso.nonDegenerate d := by
  rw [mem_nonDegenerate_iff]
  intro i
  simp only [simplexEquiv_alt, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | omega | cases b <;> decide

private lemma δ_zero_alt (b : Bool) (d : ℕ) : coherentIso.δ 0 (alt.{u} b (d + 1)) = alt (!b) d := by
  apply simplexEquiv.injective
  funext i
  simp only [simplexEquiv_δ, Function.comp_apply, Fin.succAbove_zero, simplexEquiv_alt,
    Fin.val_succ, Bool.not_not]
  split_ifs <;> first | omega | rfl

private lemma eq_alt {d : ℕ} (x : coherentIso.{u} _⦋d⦌) (hx : x ∈ coherentIso.nonDegenerate d) :
    x = alt (simplexEquiv x 0) d := by
  rw [mem_nonDegenerate_iff] at hx
  apply simplexEquiv.injective
  funext i
  induction i using Fin.induction with
  | zero => rw [simplexEquiv_alt_zero]
  | succ i ih =>
    have key : ∀ a c : Bool, a ≠ c → c = !a := by decide
    rw [key _ _ (hx i), ih, simplexEquiv_alt, simplexEquiv_alt]
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> first | omega | simp

private def pairingCore (b : Bool) (k : ℕ) (A : coherentIso.{u}.Subcomplex)
    (hA : ∀ (d : ℕ) (x : coherentIso.{u} _⦋d⦌), x ∈ coherentIso.nonDegenerate d →
      (x ∈ A.obj _ ↔ d < k ∨ (d = k ∧ simplexEquiv x 0 = b))) : A.PairingCore where
  ι := ℕ
  dim s := s + k
  simplex s := alt b (s + k + 1)
  index _ := 0
  nonDegenerate₁ _ := alt_mem_nonDegenerate _ _
  nonDegenerate₂ s := by
    rw [δ_zero_alt]
    exact alt_mem_nonDegenerate _ _
  notMem₁ s h := by
    rw [hA _ _ (alt_mem_nonDegenerate _ _)] at h
    rcases h with h | ⟨h, -⟩ <;> omega
  notMem₂ s h := by
    rw [δ_zero_alt, hA _ _ (alt_mem_nonDegenerate _ _), simplexEquiv_alt_zero] at h
    rcases h with h | ⟨-, h⟩
    · omega
    · cases b <;> simp at h
  injective_type₁' h := by
    have := S.dim_eq_of_mk_eq h
    omega
  injective_type₂' h := by
    have := S.dim_eq_of_mk_eq h
    omega
  type₁_ne_type₂' s t h := by
    have := congrArg (fun x : coherentIso.{u}.S ↦ simplexEquiv x.simplex 0) h
    simp only [δ_zero_alt, simplexEquiv_alt_zero] at this
    cases b <;> simp at this
  surjective' x := by
    obtain ⟨d, x, hx, hxA, rfl⟩ := Subcomplex.N.mk_surjective x
    rw [hA _ _ hx] at hxA
    by_cases h0 : simplexEquiv x 0 = b
    · obtain ⟨s, rfl⟩ : ∃ s, d = s + k + 1 := ⟨d - k - 1, by grind⟩
      exact ⟨s, Or.inl (congrArg S.mk ((eq_alt x hx).trans (congrArg (alt · _) h0)))⟩
    · obtain ⟨s, rfl⟩ : ∃ s, d = s + k := ⟨d - k, by omega⟩
      refine ⟨s, Or.inr (congrArg S.mk ((eq_alt x hx).trans ?_))⟩
      rw [δ_zero_alt]
      congr 1
      cases b <;> simpa using h0

private lemma eq_zero_of_δ_alt_eq (b : Bool) (D : ℕ) (i : Fin (D + 2))
    (hi : coherentIso.δ i (alt.{u} b (D + 1)) = coherentIso.δ 0 (alt b (D + 1))) : i = 0 := by
  by_contra hi0
  have := congrFun (congrArg simplexEquiv hi) 0
  rw [simplexEquiv_δ, simplexEquiv_δ, Function.comp_apply, Function.comp_apply,
    Fin.succAbove_ne_zero_zero hi0, Fin.succAbove_zero, simplexEquiv_alt, simplexEquiv_alt] at this
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_mod] at this
  cases b <;> simp at this

private instance (b : Bool) (k : ℕ) (A : coherentIso.{u}.Subcomplex)
    (hA : ∀ (d : ℕ) (x : coherentIso.{u} _⦋d⦌), x ∈ coherentIso.nonDegenerate d →
      (x ∈ A.obj _ ↔ d < k ∨ (d = k ∧ simplexEquiv x 0 = b))) :
    (pairingCore b k A hA).IsProper where
  isUniquelyCodimOneFace _ :=
    (S.IsUniquelyCodimOneFace.iff _ _).2 ⟨0, rfl, fun i hi ↦ eq_zero_of_δ_alt_eq b _ i hi⟩

private lemma eq_of_add_eq_add {a b k : ℕ} (h : a + k = b + k) : a = b := by
  omega

private instance (b : Bool) (k : ℕ) (A : coherentIso.{u}.Subcomplex)
    (hA : ∀ (d : ℕ) (x : coherentIso.{u} _⦋d⦌), x ∈ coherentIso.nonDegenerate d →
      (x ∈ A.obj _ ↔ d < k ∨ (d = k ∧ simplexEquiv x 0 = b))) :
    (pairingCore b k A hA).IsRegular :=
  (⟨fun _ ↦ (0 : ℕ), fun hxy hd ↦ (hxy.1 (eq_of_add_eq_add (k := k) hd)).elim⟩ :
      (pairingCore b k A hA).WeakRankFunction ℕ).isRegular

lemma hasLiftingProperty_ι_of_horn_zero (b : Bool) (k : ℕ)
    (A : coherentIso.{u}.Subcomplex)
    (hA : ∀ (d : ℕ) (x : coherentIso.{u} _⦋d⦌), x ∈ coherentIso.nonDegenerate d →
      (x ∈ A.obj _ ↔ d < k ∨ (d = k ∧ simplexEquiv x 0 = b)))
    {E B : SSet.{u}} (q : E ⟶ B) (hq : ∀ n : ℕ, HasLiftingProperty Λ[n + 1, 0].ι q) :
    HasLiftingProperty A.ι q :=
  hasLiftingProperty_ι_of_pairingCore (pairingCore b k A hA) q fun _ ↦ hq _

private lemma simplexEquiv_yonedaEquiv_symm_app {m d : ℕ} (v : coherentIso.{u} _⦋m⦌)
    (y : Δ[m] _⦋d⦌) (i : Fin (d + 1)) :
    simplexEquiv ((yonedaEquiv.symm v).app _ y) i =
      simplexEquiv v ((stdSimplex.objEquiv y).toOrderHom i) :=
  rfl

private lemma simplexEquiv_vertex (b : Bool) :
    simplexEquiv (cond b x₁.{u} x₀) = fun _ ↦ b := by
  funext i
  fin_cases i
  cases b <;> rfl

private lemma simplexEquiv_hom_edge : simplexEquiv hom.{u}.edge = ![false, true] := by
  funext i
  fin_cases i <;> rfl

private lemma mem_range_vertex_iff (b : Bool) (d : ℕ) (x : coherentIso.{u} _⦋d⦌)
    (hx : x ∈ coherentIso.nonDegenerate d) :
    x ∈ (Subcomplex.range (yonedaEquiv.symm (cond b x₁ x₀) : Δ[0] ⟶ coherentIso.{u})).obj _ ↔
      d < 0 ∨ (d = 0 ∧ simplexEquiv x 0 = b) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hc (i : Fin (d + 1)) :
        simplexEquiv ((yonedaEquiv.symm (cond b x₁ x₀)).app _ y) i = b := by
      rw [simplexEquiv_yonedaEquiv_symm_app, simplexEquiv_vertex]
    cases d with
    | zero => exact Or.inr ⟨rfl, hc 0⟩
    | succ d => exact absurd ((hc _).trans (hc _).symm) ((mem_nonDegenerate_iff _).1 hx 0)
  · rintro (h | ⟨rfl, h⟩)
    · omega
    · refine ⟨yonedaEquiv (𝟙 _), ?_⟩
      rw [yonedaEquiv_symm_app_id]
      apply simplexEquiv.injective
      funext i
      fin_cases i
      rw [simplexEquiv_vertex]
      exact h.symm

lemma mem_range_hom_iff (d : ℕ) (x : coherentIso.{u} _⦋d⦌)
    (hx : x ∈ coherentIso.nonDegenerate d) :
    x ∈ (Subcomplex.range (yonedaEquiv.symm hom.edge : Δ[1] ⟶ coherentIso.{u})).obj _ ↔
      d < 1 ∨ (d = 1 ∧ simplexEquiv x 0 = false) := by
  rw [mem_nonDegenerate_iff] at hx
  constructor
  · rintro ⟨y, rfl⟩
    have hc (i : Fin (d + 1)) : simplexEquiv ((yonedaEquiv.symm hom.edge).app _ y) i =
        ![false, true] ((stdSimplex.objEquiv y).toOrderHom i) := by
      rw [simplexEquiv_yonedaEquiv_symm_app, simplexEquiv_hom_edge]
    have hm := (stdSimplex.objEquiv y).toOrderHom.monotone
    simp only [hc] at hx ⊢
    have key : ∀ a c : Fin 2, a ≤ c → ![false, true] a ≠ ![false, true] c → a = 0 ∧ c = 1 := by
      decide
    obtain _ | _ | d := d
    · exact Or.inl (by omega)
    · exact Or.inr ⟨rfl, congrArg ![false, true] (key _ _ (hm (Fin.castSucc_le_succ 0)) (hx 0)).1⟩
    · have h₁ := (key _ _ (hm (Fin.castSucc_le_succ 0)) (hx 0)).2
      have h₂ := (key _ _ (hm (Fin.castSucc_le_succ 1)) (hx 1)).1
      rw [show Fin.castSucc (1 : Fin (d + 2)) = Fin.succ 0 from rfl, h₁] at h₂
      exact absurd h₂ (by decide)
  · rintro (h | ⟨rfl, h⟩)
    · obtain rfl : d = 0 := by omega
      refine ⟨stdSimplex.objEquiv.symm (SimplexCategory.const _ _
        (bif simplexEquiv x 0 then 1 else 0)), simplexEquiv.injective (funext fun i ↦ ?_)⟩
      obtain rfl := Fin.fin_one_eq_zero i
      rw [simplexEquiv_yonedaEquiv_symm_app, simplexEquiv_hom_edge]
      cases simplexEquiv x 0 <;> rfl
    · refine ⟨yonedaEquiv (𝟙 _), ?_⟩
      rw [yonedaEquiv_symm_app_id]
      have key : ∀ a c : Bool, a ≠ c → c = !a := by decide
      apply simplexEquiv.injective
      funext i
      induction i using Fin.cases with
      | zero =>
        rw [simplexEquiv_hom_edge]
        exact h.symm
      | succ j =>
        obtain rfl := Fin.fin_one_eq_zero j
        rw [simplexEquiv_hom_edge, key _ _ (hx 0), Fin.castSucc_zero, h]
        rfl

private lemma nonempty_invStruct (e : coherentIso.{u} _⦋1⦌) : Nonempty (Edge.mk' e).InvStruct := by
  have h₀ : coherentIso.δ 1 e = cond (simplexEquiv e 0) x₁ x₀ := by
    apply simplexEquiv.injective
    rw [simplexEquiv_vertex]
    funext i
    fin_cases i
    rfl
  have h₁ : coherentIso.δ 0 e = cond (simplexEquiv e 1) x₁ x₀ := by
    apply simplexEquiv.injective
    rw [simplexEquiv_vertex]
    funext i
    fin_cases i
    rfl
  have he : ∀ (e' : coherentIso.{u} _⦋1⦌), simplexEquiv e' = simplexEquiv e →
      Nonempty (Edge.mk' e').InvStruct → Nonempty (Edge.mk' e).InvStruct := by
    intro e' h₂ hI
    obtain rfl : e' = e := simplexEquiv.injective h₂
    exact hI
  generalize ha : simplexEquiv e 0 = a at h₀
  generalize hc : simplexEquiv e 1 = c at h₁
  cases a <;> cases c
  · refine he (Edge.id x₀).edge (funext fun i ↦ ?_) ⟨(Edge.InvStruct.invStructId _).ofEq rfl⟩
    fin_cases i <;> simp [ha, hc] <;> rfl
  · refine he hom.edge (funext fun i ↦ ?_) ⟨invStructHom.ofEq rfl⟩
    fin_cases i <;> simp [ha, hc, simplexEquiv_hom_edge]
  · refine he inv.edge (funext fun i ↦ ?_) ⟨invStructHom.invStructInv.ofEq rfl⟩
    fin_cases i <;> simp [ha, hc] <;> rfl
  · refine he (Edge.id x₁).edge (funext fun i ↦ ?_) ⟨(Edge.InvStruct.invStructId _).ofEq rfl⟩
    fin_cases i <;> simp [ha, hc] <;> rfl

lemma nonempty_invStruct_app {X : SSet.{u}} (g : coherentIso.{u} ⟶ X)
    (e : coherentIso.{u} _⦋1⦌) : Nonempty (Edge.mk' (g.app _ e)).InvStruct :=
  ⟨((nonempty_invStruct e).some.map g).ofEq rfl⟩

private lemma mono_vertex (b : Bool) :
    Mono (yonedaEquiv.symm (cond b x₁ x₀) : Δ[0] ⟶ coherentIso.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro y y' _
  exact stdSimplex.objEquiv.injective (SimplexCategory.Hom.ext _ _
    (OrderHom.ext _ _ (funext fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)))

lemma mono_hom_edge : Mono (yonedaEquiv.symm hom.edge : Δ[1] ⟶ coherentIso.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨n⟩
  induction n using SimplexCategory.rec with | _ d => ?_
  rw [mono_iff_injective]
  intro y y' h
  have hinj : Function.Injective (![false, true] : Fin 2 → Bool) := by decide
  refine stdSimplex.objEquiv.injective (SimplexCategory.Hom.ext _ _
    (OrderHom.ext _ _ (funext fun i ↦ hinj ?_)))
  have := congrFun (congrArg simplexEquiv h) i
  rwa [simplexEquiv_yonedaEquiv_symm_app, simplexEquiv_yonedaEquiv_symm_app,
    simplexEquiv_hom_edge] at this

end coherentIso

section Lifting

lemma hasLiftingProperty_of_range_ι {A B E S : SSet.{u}} (f : A ⟶ B) [Mono f]
    (p : E ⟶ S) (h : HasLiftingProperty (Subcomplex.range f).ι p) : HasLiftingProperty f p :=
  (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk (asIso (Subfunctor.toRange f)).symm
    (Iso.refl _) ((Iso.inv_comp_eq (asIso (Subfunctor.toRange f))).2
      ((Subfunctor.toRange_ι f).symm.trans
      (congrArg _ (Category.comp_id _).symm)))) p).1 h

private lemma hasLiftingProperty_of_coreMap {A B X Y : SSet.{u}} [X.Quasicategory] (i : A ⟶ B)
    (p : X ⟶ Y) (hA : ∀ e : A _⦋1⦌, Nonempty (Edge.mk' e).InvStruct)
    (hB : ∀ e : B _⦋1⦌, Nonempty (Edge.mk' e).InvStruct)
    (h : HasLiftingProperty i (coreMap p)) : HasLiftingProperty i p := by
  refine ⟨fun {u v} sq ↦ ?_⟩
  have sq' : CommSq (Subcomplex.lift u (range_le_core u hA)) i (coreMap p)
      (Subcomplex.lift v (range_le_core v hB)) := ⟨by
    rw [← cancel_mono Y.core.ι, Category.assoc, coreMap_ι, Subcomplex.lift_ι_assoc, sq.w,
      Category.assoc, Subcomplex.lift_ι]⟩
  exact ⟨⟨⟨sq'.lift ≫ X.core.ι, by rw [sq'.fac_left_assoc, Subcomplex.lift_ι], by
    rw [Category.assoc, ← coreMap_ι, ← Category.assoc, sq'.fac_right, Subcomplex.lift_ι]⟩⟩⟩

theorem hasLiftingProperty_coherentIso_vertex_of_horn_zero (b : Bool) {E B : SSet.{u}}
    (q : E ⟶ B) (hq : ∀ n : ℕ, HasLiftingProperty Λ[n + 1, 0].ι q) :
    HasLiftingProperty (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) q := by
  have := coherentIso.mono_vertex.{u} b
  exact hasLiftingProperty_of_range_ι _ _ (coherentIso.hasLiftingProperty_ι_of_horn_zero b 0 _
    (coherentIso.mem_range_vertex_iff b) q hq)

theorem hasLiftingProperty_coherentIso_vertex (b : Bool) {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Isofibration p] :
    HasLiftingProperty (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) p := by
  refine hasLiftingProperty_of_coreMap _ p (fun e ↦
    ⟨(Edge.InvStruct.invStructId (Δ[0].δ 1 e)).ofEq (hom' := Edge.mk' e)
      (yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _))⟩)
    coherentIso.nonempty_invStruct ?_
  exact hasLiftingProperty_coherentIso_vertex_of_horn_zero b _
    (hasLiftingProperty_horn_zero_coreMap p)

theorem rightAnodyneExtensions_coherentIso_vertex (b : Bool) :
    rightAnodyneExtensions (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) := by
  intro E S q hq
  refine ⟨fun {u v} sq ↦ ?_⟩
  have hq' : rightFibrations (pullback.snd q v) :=
    MorphismProperty.pullback_snd (P := rightHornInclusions.rlp) _ _ hq
  have : InnerFibration (pullback.snd q v) := innerFibration_of_rightFibrations hq'
  have := quasicategory_of_innerFibration (pullback.snd q v)
  have : Isofibration (pullback.snd q v) :=
    { exists_lift := fun _ _ g hg ↦ by
        obtain ⟨x₁, f, hf⟩ := exists_edge_map_eq_of_rightFibrations hq' g hg
        exact ⟨x₁, f, nonempty_invStruct_of_rightFibrations hq' f ⟨hg.some.ofEq hf.symm⟩, hf⟩ }
  have sq' : CommSq (pullback.lift u _ sq.w)
      (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀)) (pullback.snd q v) (𝟙 _) :=
    ⟨by rw [pullback.lift_snd, Category.comp_id]⟩
  obtain ⟨l⟩ := ((hasLiftingProperty_coherentIso_vertex b (pullback.snd q v)).sq_hasLift
    sq').exists_lift
  exact ⟨⟨⟨l.l ≫ pullback.fst q v, by rw [← Category.assoc, l.fac_left, pullback.lift_fst], by
    rw [Category.assoc, pullback.condition, ← Category.assoc, l.fac_right, Category.id_comp]⟩⟩⟩

theorem exists_coherentIso_extension {X : SSet.{u}} [X.Quasicategory] {x y : X _⦋0⦌}
    (e : Edge x y) (h : e.InvStruct) :
    ∃ g : coherentIso.{u} ⟶ X, (coherentIso.hom.map g).edge = e.edge := by
  have := coherentIso.mono_hom_edge.{u}
  have : IsIso (terminal.from (⊤_ SSet.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  have : (⊤_ SSet.{u}).Quasicategory := by
    rw [quasicategory_iff_innerFibration]
    exact ⟨rlp_of_isIso _ _⟩
  have hlift : HasLiftingProperty (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})
      (coreMap (terminal.from X)) := by
    refine hasLiftingProperty_of_range_ι _ _ ?_
    exact coherentIso.hasLiftingProperty_ι_of_horn_zero false 1 _ coherentIso.mem_range_hom_iff
      _ (hasLiftingProperty_horn_zero_coreMap _)
  have he : e.edge ∈ X.core.obj _ := edge_mem_core_of_isIso e h.isIso_homMk
  have hu : Subcomplex.range (yonedaEquiv.symm e.edge) ≤ X.core := by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, Equiv.apply_symm_apply]
    exact he
  have sq : CommSq (Subcomplex.lift _ hu) (yonedaEquiv.symm coherentIso.hom.edge)
      (coreMap (terminal.from X)) (Subcomplex.lift _ (range_le_core (terminal.from coherentIso)
        coherentIso.nonempty_invStruct)) :=
    ⟨by rw [← cancel_mono (⊤_ SSet.{u}).core.ι]; exact terminal.hom_ext _ _⟩
  obtain ⟨l⟩ := (hlift.sq_hasLift sq).exists_lift
  refine ⟨l.l ≫ X.core.ι, ?_⟩
  calc (coherentIso.hom.map (l.l ≫ X.core.ι)).edge
      = yonedaEquiv (yonedaEquiv.symm coherentIso.hom.edge ≫ l.l ≫ X.core.ι) := by
        rw [Edge.map_edge, yonedaEquiv_comp, Equiv.apply_symm_apply]
    _ = yonedaEquiv (Subcomplex.lift _ hu ≫ X.core.ι) := by rw [← Category.assoc, l.fac_left]
    _ = e.edge := by rw [Subcomplex.lift_ι, Equiv.apply_symm_apply]

theorem Isofibration.of_hasLiftingProperty_vertex {E B : SSet.{u}} (q : E ⟶ B)
    [InnerFibration q] [B.Quasicategory]
    (h : HasLiftingProperty (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) q) :
    Isofibration q where
  exists_lift x₀ _ g hg := by
    obtain ⟨G, hG⟩ := exists_coherentIso_extension g hg.some
    have hG₀ : G.app _ coherentIso.x₀ = q.app _ x₀ :=
      calc G.app _ coherentIso.x₀ = G.app _ (coherentIso.δ 1 coherentIso.hom.edge) :=
            congrArg _ coherentIso.hom.src_eq.symm
        _ = B.δ 1 (G.app _ coherentIso.hom.edge) := NatTrans.naturality_apply G _ _
        _ = B.δ 1 g.edge := congrArg _ hG
        _ = q.app _ x₀ := g.src_eq
    have sq : CommSq (yonedaEquiv.symm x₀) (yonedaEquiv.symm coherentIso.x₀) q G :=
      ⟨yonedaEquiv.injective (by rw [yonedaEquiv_comp, yonedaEquiv_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply, hG₀])⟩
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    have h₀ : l.l.app _ coherentIso.x₀ = x₀ := by
      have := congrArg yonedaEquiv l.fac_left
      rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    have hl : q.app _ (l.l.app _ coherentIso.hom.edge) = g.edge :=
      (ConcreteCategory.congr_hom (congr_app l.fac_right _) coherentIso.hom.edge).trans hG
    exact ⟨_, (coherentIso.hom.map l.l).ofEq h₀ rfl,
      ⟨coherentIso.invStructOfEqMapHom rfl⟩, hl⟩

theorem isofibration_of_isPullback {P E B Z : SSet.{u}} {f : P ⟶ E} {q' : P ⟶ Z} {q : E ⟶ B}
    {g : Z ⟶ B} (h : IsPullback f q' q g) [Isofibration q] [E.Quasicategory] [B.Quasicategory]
    [Z.Quasicategory] : Isofibration q' := by
  have : InnerFibration q' := ⟨MorphismProperty.of_isPullback (P := innerFibrations) h
    (mem_innerFibrations q)⟩
  have : HasLiftingProperty (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) q :=
    hasLiftingProperty_coherentIso_vertex false q
  exact Isofibration.of_hasLiftingProperty_vertex _ (h.hasLiftingProperty _)

end Lifting

section Slices

theorem isofibration_slice_map {Z E B : SSet.{u}} [E.Quasicategory] [B.Quasicategory]
    (p : E ⟶ B) [Isofibration p] (z : Z ⟶ E) :
    Isofibration ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) := by
  have : InnerFibration ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) :=
    ⟨fun _ _ _ ⟨k, h0, hn⟩ ↦
      have : HasLiftingProperty Λ[_ + 2, k].ι p := mem_innerFibrations p _ (.intro k h0 hn)
      hasLiftingProperty_slice_map (rightAnodyneExtensions.horn_ι h0) p z⟩
  have : (Under.mk (z ≫ p)).right.Quasicategory := ‹B.Quasicategory›
  have := hasLiftingProperty_coherentIso_vertex false p
  exact Isofibration.of_hasLiftingProperty_vertex _
    (hasLiftingProperty_slice_map (rightAnodyneExtensions_coherentIso_vertex false) p z)

end Slices

theorem nonempty_invStruct_of_kanComplex (K : SSet.{u}) [K.KanComplex] (e : K _⦋1⦌) :
    Nonempty (SSet.Edge.mk' e).InvStruct := by
  have hr : SSet.rightFibrations (terminal.from K) := by
    rintro _ _ _ ⟨i, -⟩
    exact ⟨fun {a _} _ => by
      obtain ⟨σ, hσ⟩ := SSet.KanComplex.hornFilling a
      exact ⟨⟨⟨σ, hσ.symm, terminal.hom_ext _ _⟩⟩⟩⟩
  exact SSet.nonempty_invStruct_of_rightFibrations hr (SSet.Edge.mk' e)
    ⟨(SSet.Edge.InvStruct.invStructId ((terminal.from K).app _ (K.δ 1 e))).ofEq
      (hom' := (SSet.Edge.mk' e).map (terminal.from K))
      (SSet.yonedaEquiv.symm.injective (terminal.hom_ext _ _))⟩

end SSet
