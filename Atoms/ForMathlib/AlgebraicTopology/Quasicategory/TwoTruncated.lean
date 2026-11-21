import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

open CategoryTheory Simplicial SimplicialObject.Truncated

universe u

local macro "compatible_cases" : tactic =>
  `(tactic| (intro j k hj hk hjk
             fin_cases j <;> fin_cases k
             all_goals try exact absurd hjk (by decide)
             all_goals try exact (hj rfl).elim
             all_goals try exact (hk rfl).elim))

namespace SSet

namespace Quasicategory

variable {X : SSet.{u}} [X.Quasicategory]

private lemma exists_simplex_δ_eq {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) (s : ∀ j : Fin (n + 3), j ≠ i → X _⦋n + 1⦌)
    (hs : ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (s j hj) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (s k hk)) :
    ∃ τ : X _⦋n + 2⦌, ∀ (j : Fin (n + 3)) (hj : j ≠ i), X.δ j τ = s j hj := by
  have hc : horn.IsCompatible (fun j hj ↦ yonedaEquiv.symm (s j hj)) := by
    intro j k hj hk hjk
    simp only [stdSimplex.δ_comp_yonedaEquiv_symm, hs j k hj hk hjk]
  obtain ⟨σ, hσ⟩ := hornFilling h0 hn hc.desc
  refine ⟨yonedaEquiv σ, fun j hj ↦ ?_⟩
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι i j hj, Category.assoc, ← hσ,
    hc.ι_desc, Equiv.apply_symm_apply]

instance quasicategory₂ : ((truncation 2).obj X).Quasicategory₂ where
  fill21 {x₀ x₁ x₂} e₀₁ e₁₂ := by
    obtain ⟨τ, hτ⟩ := exists_simplex_δ_eq (X := X) (i := 1) (by decide) (by decide)
      (fun j _ ↦ ![e₁₂.edge, e₁₂.edge, e₀₁.edge] j) (by
        compatible_cases
        exact (Edge.src_eq (X := X) e₁₂).trans (Edge.tgt_eq (X := X) e₀₁).symm)
    exact ⟨⟨Edge.mk (X := X) (X.δ 1 τ)
      ((δ_comp_δ_self_apply (i := 1) τ).trans
        ((congrArg (X.δ 1) (hτ 2 (by decide))).trans (Edge.src_eq (X := X) e₀₁)))
      ((δ_comp_δ_self_apply (i := 0) τ).symm.trans
        ((congrArg (X.δ 0) (hτ 0 (by decide))).trans (Edge.tgt_eq (X := X) e₁₂))),
      Edge.CompStruct.mk (X := X) τ (hτ 2 (by decide)) (hτ 0 (by decide)) rfl⟩⟩
  fill31 {x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃} f₃ f₀ f₂ := by
    obtain ⟨τ, hτ⟩ := exists_simplex_δ_eq (X := X) (i := 1) (by decide) (by decide)
      (fun j _ ↦ ![f₀.simplex, f₀.simplex, f₂.simplex, f₃.simplex] j) (by
        compatible_cases
        exacts [f₀.d₁.trans f₂.d₀.symm, f₀.d₂.trans f₃.d₀.symm, f₂.d₂.trans f₃.d₂.symm])
    exact ⟨Edge.CompStruct.mk (X := X) (X.δ 1 τ)
      ((δ_comp_δ_apply (i := 1) (j := 2) (by decide) τ).symm.trans
        ((congrArg (X.δ 1) (hτ 3 (by decide))).trans f₃.d₁))
      ((δ_comp_δ_self_apply (i := 0) τ).symm.trans
        ((congrArg (X.δ 0) (hτ 0 (by decide))).trans f₀.d₀))
      ((δ_comp_δ_self_apply (i := 1) τ).trans
        ((congrArg (X.δ 1) (hτ 2 (by decide))).trans f₂.d₁))⟩
  fill32 {x₀ x₁ x₂ x₃ e₀₁ e₁₂ e₂₃ e₀₂ e₁₃ e₀₃} f₃ f₀ f₁ := by
    obtain ⟨τ, hτ⟩ := exists_simplex_δ_eq (X := X) (i := 2) (by decide) (by decide)
      (fun j _ ↦ ![f₀.simplex, f₁.simplex, f₀.simplex, f₃.simplex] j) (by
        compatible_cases
        exacts [f₀.d₀.trans f₁.d₀.symm, f₀.d₂.trans f₃.d₀.symm, f₁.d₂.trans f₃.d₁.symm])
    exact ⟨Edge.CompStruct.mk (X := X) (X.δ 2 τ)
      ((δ_comp_δ_self_apply (i := 2) τ).trans
        ((congrArg (X.δ 2) (hτ 3 (by decide))).trans f₃.d₂))
      ((δ_comp_δ_apply (i := 0) (j := 1) (by decide) τ).trans
        ((congrArg (X.δ 1) (hτ 0 (by decide))).trans f₀.d₁))
      ((δ_comp_δ_self_apply (i := 1) τ).symm.trans
        ((congrArg (X.δ 1) (hτ 1 (by decide))).trans f₁.d₁))⟩

end Quasicategory

namespace Truncated

variable {A : Truncated.{u} 2} [A.Quasicategory₂]

namespace HomotopyCategory₂

private noncomputable def ofHomotopyCategory : A.HomotopyCategory ⥤ HomotopyCategory₂ A :=
  HomotopyCategory.lift (fun x ↦ mk x) (fun e ↦ homMk e) (fun x ↦ homMk_id (mk x))
    (fun h ↦ h.homotopyCategory₂_fac)

private lemma ofHomotopyCategory_map_homMk {x y : A _⦋0⦌₂} (e : Edge x y) :
    ofHomotopyCategory.map (HomotopyCategory.homMk e) = homMk e :=
  HomotopyCategory.lift_map_homMk ..

end HomotopyCategory₂

open HomotopyCategory₂ in
theorem HomotopyCategory.homMk_eq_homMk_iff {x y : A _⦋0⦌₂} (e e' : Edge x y) :
    HomotopyCategory.homMk e = HomotopyCategory.homMk e' ↔ HomotopicL e e' := by
  refine ⟨fun h ↦ Quotient.exact ((ofHomotopyCategory_map_homMk e).symm.trans
    ((congrArg ofHomotopyCategory.map h).trans (ofHomotopyCategory_map_homMk e'))), ?_⟩
  rintro ⟨h⟩
  rw [← HomotopyCategory.homMk_comp_homMk h, HomotopyCategory.homMk_id, Category.comp_id]

namespace HomotopyCategory₂

private def toHomotopyCategory : HomotopyCategory₂ A ⥤ A.HomotopyCategory where
  obj x := HomotopyCategory.mk x.pt
  map := Quotient.lift (fun e ↦ HomotopyCategory.homMk e)
    (fun e e' h ↦ (HomotopyCategory.homMk_eq_homMk_iff e e').2 h)
  map_id x := HomotopyCategory.homMk_id x.pt
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact (HomotopyCategory.homMk_comp_homMk (Edge.compStruct f g)).symm

private lemma toHomotopyCategory_map_homMk {x y : A _⦋0⦌₂} (e : Edge x y) :
    toHomotopyCategory.map (homMk e) = HomotopyCategory.homMk e :=
  rfl

variable (A) in
noncomputable def equivalence : HomotopyCategory₂ A ≌ A.HomotopyCategory :=
  CategoryTheory.Equivalence.mk toHomotopyCategory ofHomotopyCategory
    (NatIso.ofComponents (fun x ↦ Iso.refl x) (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain ⟨e, rfl⟩ := homMk_surjective f
      simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom, toHomotopyCategory_map_homMk]
      exact (Category.comp_id _).trans
        ((ofHomotopyCategory_map_homMk e).symm.trans (Category.id_comp _).symm)))
    (HomotopyCategory.mkNatIso (fun x ↦ Iso.refl _) (fun _ _ e ↦ by
      simp only [Functor.id_map, Functor.comp_map, Iso.refl_hom, ofHomotopyCategory_map_homMk]
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

@[simp]
lemma equivalence_functor_obj (x : A _⦋0⦌₂) :
    (equivalence A).functor.obj (mk x) = HomotopyCategory.mk x :=
  rfl

@[simp]
lemma equivalence_functor_map_homMk {x y : A _⦋0⦌₂} (e : Edge x y) :
    (equivalence A).functor.map (homMk e) = HomotopyCategory.homMk e :=
  rfl

end HomotopyCategory₂

open HomotopyCategory₂ in
theorem HomotopyCategory.homMk_surjective {x y : A _⦋0⦌₂}
    (f : HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) :
    ∃ e : Edge x y, HomotopyCategory.homMk e = f := by
  obtain ⟨e, he⟩ := HomotopyCategory₂.homMk_surjective (ofHomotopyCategory.map f)
  exact ⟨e, (equivalence A).inverse.map_injective ((ofHomotopyCategory_map_homMk e).trans he)⟩

open HomotopyCategory₂ in
private lemma nonempty_compStruct_of_homMk_comp_homMk {x y z : A _⦋0⦌₂} {f : Edge x y}
    {g : Edge y z} {h : Edge x z}
    (fac : HomotopyCategory.homMk f ≫ HomotopyCategory.homMk g = HomotopyCategory.homMk h) :
    Nonempty (Edge.CompStruct f g h) := by
  have hfac := congrArg ofHomotopyCategory.map fac
  rw [Functor.map_comp] at hfac
  simp only [ofHomotopyCategory_map_homMk] at hfac
  exact Edge.CompStruct.nonempty_iff.2 hfac

end Truncated

theorem Edge.InvStruct.isIso_homMk {X : SSet.{u}} {x y : X _⦋0⦌} {e : Edge x y}
    (h : e.InvStruct) : IsIso (Truncated.HomotopyCategory.homMk e) :=
  ⟨Truncated.HomotopyCategory.homMk h.inv,
    (Truncated.HomotopyCategory.homMk_comp_homMk h.homInvId).trans
      (Truncated.HomotopyCategory.homMk_id _),
    (Truncated.HomotopyCategory.homMk_comp_homMk h.invHomId).trans
      (Truncated.HomotopyCategory.homMk_id _)⟩

theorem isIso_homMk_iff {X : SSet.{u}} [X.Quasicategory] {x y : X _⦋0⦌} (e : Edge x y) :
    IsIso (Truncated.HomotopyCategory.homMk e) ↔ Nonempty e.InvStruct := by
  refine ⟨fun _ ↦ ?_, fun ⟨h⟩ ↦ h.isIso_homMk⟩
  obtain ⟨e', he'⟩ := Truncated.HomotopyCategory.homMk_surjective
    (inv (Truncated.HomotopyCategory.homMk e))
  obtain ⟨s⟩ := Truncated.nonempty_compStruct_of_homMk_comp_homMk (f := e) (g := e')
    (h := Edge.id x) (by
    rw [he', IsIso.hom_inv_id]
    exact (Truncated.HomotopyCategory.homMk_id _).symm)
  obtain ⟨s'⟩ := Truncated.nonempty_compStruct_of_homMk_comp_homMk (f := e') (g := e)
    (h := Edge.id y) (by
    rw [he', IsIso.inv_hom_id]
    exact (Truncated.HomotopyCategory.homMk_id _).symm)
  exact ⟨⟨e', .ofTruncated s, .ofTruncated s'⟩⟩

theorem nonempty_invStruct_congr {X : SSet.{u}} {e e' : X _⦋1⦌} (h : e = e')
    (he : Nonempty (Edge.mk' e).InvStruct) : Nonempty (Edge.mk' e').InvStruct :=
  h ▸ he

theorem nonempty_invStruct_σ {X : SSet.{u}} (x : X _⦋0⦌) :
    Nonempty (Edge.mk' (X.σ 0 x)).InvStruct :=
  ⟨(Edge.InvStruct.invStructId x).ofEq rfl⟩

section TwoOutOfThree

variable {X : SSet.{u}} [X.Quasicategory] (σ : X _⦋2⦌)

private theorem nonempty_invStruct_of_simplex :
    (Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct →
      Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct) ∧
    (Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct →
      Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct) ∧
    (Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct →
      Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct) := by
  let e₁₂ : Edge (X.δ 0 (X.δ 2 σ)) (X.δ 0 (X.δ 0 σ)) := Edge.mk (X.δ 0 σ)
    (δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ).symm rfl
  let e₀₂ : Edge (X.δ 1 (X.δ 2 σ)) (X.δ 0 (X.δ 0 σ)) := Edge.mk (X.δ 1 σ)
    (δ_comp_δ_self_apply (i := 1) σ) (δ_comp_δ_self_apply (i := 0) σ).symm
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk
    (Edge.CompStruct.mk (e₀₁ := Edge.mk' (X.δ 2 σ)) (e₁₂ := e₁₂) (e₀₂ := e₀₂) σ rfl rfl rfl)
  have h₁₂ : Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct ↔ Nonempty e₁₂.InvStruct :=
    ⟨fun ⟨I⟩ ↦ ⟨I.ofEq rfl⟩, fun ⟨I⟩ ↦ ⟨I.ofEq rfl⟩⟩
  have h₀₂ : Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct ↔ Nonempty e₀₂.InvStruct :=
    ⟨fun ⟨I⟩ ↦ ⟨I.ofEq rfl⟩, fun ⟨I⟩ ↦ ⟨I.ofEq rfl⟩⟩
  rw [h₁₂, h₀₂, ← isIso_homMk_iff, ← isIso_homMk_iff, ← isIso_homMk_iff]
  refine ⟨fun h₂ h₀ ↦ ?_, fun h₂ h₁ ↦ ?_, fun h₀ h₁ ↦ ?_⟩
  · exact (congrArg IsIso hc).mp (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₀)
  · exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (Truncated.HomotopyCategory.homMk (Edge.mk' (X.δ 2 σ)).toTruncated) _ h₂
      ((congrArg IsIso hc).mpr h₁)
  · exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
      (Truncated.HomotopyCategory.homMk e₁₂.toTruncated) h₀ ((congrArg IsIso hc).mpr h₁)

theorem nonempty_invStruct_δ_one : Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct →
    Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct :=
  (nonempty_invStruct_of_simplex σ).1

theorem nonempty_invStruct_δ_zero : Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct →
    Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct :=
  (nonempty_invStruct_of_simplex σ).2.1

theorem nonempty_invStruct_δ_two : Nonempty (Edge.mk' (X.δ 0 σ)).InvStruct →
    Nonempty (Edge.mk' (X.δ 1 σ)).InvStruct → Nonempty (Edge.mk' (X.δ 2 σ)).InvStruct :=
  (nonempty_invStruct_of_simplex σ).2.2

end TwoOutOfThree

end SSet
