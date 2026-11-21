import Atoms.ForMathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Atoms.Shape.Cone.Core

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

theorem coneCoord_comp_coneHom_apply_top {T F : Atom} {r s : ℕ} (g : T ⟶ cone F r)
    (σ : Fin r →o Fin s) :
    coneCoord F s ((g ≫ coneHom F σ) T.top) =
      ((coneCoord F r (g T.top)).1, (coneCoord F r (g T.top)).2.image σ) :=
  coneCoord_coneHom F σ (g T.top)

theorem coneCoord_comp_coneMap_apply_top {T B B' : Atom} {r : ℕ} (g : T ⟶ cone B r)
    (f : B ⟶ B') :
    coneCoord B' r ((g ≫ coneMap f r) T.top) =
      ((coneCoord B r (g T.top)).1.map f, (coneCoord B r (g T.top)).2) :=
  coneCoord_coneMap f r (g T.top)

theorem coneHom_toOrderHom_comp (A : Atom) {c d e : AugmentedSimplexCategory}
    (f : c ⟶ d) (g : d ⟶ e) :
    coneHom A (AugmentedSimplexCategory.toOrderHom (f ≫ g)) =
      coneHom A (AugmentedSimplexCategory.toOrderHom f) ≫
        coneHom A (AugmentedSimplexCategory.toOrderHom g) := by
  rw [AugmentedSimplexCategory.toOrderHom_comp]
  exact (coneHom_comp A _ _).symm

theorem eqToHom_cone (F : Atom) {r s : ℕ} (h : r = s) :
    eqToHom (congrArg (cone F) h) = coneHom F ⟨Fin.cast h, fun _ _ hij => hij⟩ := by
  subst h
  rw [eqToHom_refl]
  exact (eq_coneHom _ (Category.comp_id _) fun i => Category.comp_id _).trans (by rfl)

@[reassoc] theorem coneMap_coneMap_comp_coneAssoc {F F' : Atom} (f : F ⟶ F') (k r : ℕ) :
    coneMap (coneMap f k) r ≫ (coneAssoc F' k r).hom =
      (coneAssoc F k r).hom ≫ coneMap f (k + r) :=
  cone_hom_ext (Fin.natAdd k) (fun i => by simp) (fun i => by simp) (by
    rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc, coneIncl_comp_coneAssoc_assoc,
      coneHom_comp_coneMap])

@[reassoc] theorem coneHom_comp_coneAssoc (F : Atom) (k : ℕ) {r s : ℕ} (σ : Fin r →o Fin s)
    (τ : Fin (k + r) →o Fin (k + s)) (hτ₁ : ∀ i, τ (Fin.castAdd r i) = Fin.castAdd s i)
    (hτ₂ : ∀ j, τ (Fin.natAdd k j) = Fin.natAdd k (σ j)) :
    coneHom (cone F k) σ ≫ (coneAssoc F k s).hom = (coneAssoc F k r).hom ≫ coneHom F τ :=
  cone_hom_ext (fun j => Fin.natAdd k (σ j)) (fun j => by simp) (fun j => by simp [hτ₂]) (by
    rw [coneIncl_comp_coneHom_assoc, coneIncl_comp_coneAssoc, coneIncl_comp_coneAssoc_assoc,
      coneHom_comp]
    congr 1
    exact OrderHom.ext _ _ (funext fun i => (hτ₁ i).symm))

@[reassoc] theorem coneMap_coneIncl_comp_coneAssoc (F : Atom) (k r : ℕ) :
    coneMap (coneIncl F k) r ≫ (coneAssoc F k r).hom =
      coneHom F ⟨Fin.natAdd k, fun _ _ hij => Fin.natAdd_le_natAdd_iff k |>.2 hij⟩ :=
  eq_coneHom _ (by rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc,
      coneIncl_comp_coneHom]) (fun i => by
    rw [conePoint_comp_coneMap_assoc, conePoint_comp_coneAssoc]
    rfl)

@[reassoc] theorem coneMap_coneHom_comp_coneAssoc (F : Atom) {k l : ℕ} (σ : Fin k →o Fin l)
    (r : ℕ) (τ : Fin (k + r) →o Fin (l + r)) (hτ₁ : ∀ i, τ (Fin.castAdd r i) = Fin.castAdd r (σ i))
    (hτ₂ : ∀ j, τ (Fin.natAdd k j) = Fin.natAdd l j) :
    coneMap (coneHom F σ) r ≫ (coneAssoc F l r).hom = (coneAssoc F k r).hom ≫ coneHom F τ :=
  cone_hom_ext (Fin.natAdd l) (fun j => by simp) (fun j => by simp [hτ₂]) (by
    rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc, coneIncl_comp_coneAssoc_assoc,
      coneHom_comp, coneHom_comp]
    congr 1
    exact OrderHom.ext _ _ (funext fun i => (hτ₁ i).symm))

theorem coneAssoc_hom_comp_coneAssoc_hom (F : Atom) (k l r : ℕ) :
    (coneAssoc (cone F k) l r).hom ≫ (coneAssoc F k (l + r)).hom =
      coneMap (coneAssoc F k l).hom r ≫ (coneAssoc F (k + l) r).hom ≫
        eqToHom (congrArg (cone F) (Nat.add_assoc k l r)) := by
  refine cone_hom_ext (fun i => Fin.natAdd k (Fin.natAdd l i)) (fun i => by simp)
    (fun i => by
      rw [conePoint_comp_coneMap_assoc, conePoint_comp_coneAssoc_assoc,
        eqToHom_cone F (Nat.add_assoc k l r), conePoint_comp_coneHom]
      congr 1
      exact Fin.ext (Nat.add_assoc k l i)) ?_
  rw [coneIncl_comp_coneAssoc_assoc, coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc_assoc,
    eqToHom_cone F (Nat.add_assoc k l r), coneHom_comp,
    coneHom_comp_coneAssoc F k ⟨Fin.castAdd r, fun _ _ h => h⟩ ⟨fun i => Fin.cast
      (Nat.add_assoc k l r) (Fin.castAdd r i), fun _ _ h => h⟩ (fun i => Fin.ext rfl)
      (fun j => Fin.ext rfl)]
  rfl

theorem conePoint_comp_eq_of_isCollapseHom {B B' : Atom} (q : cone B 1 ⟶ cone B' 1)
    (hq : IsCollapseHom q) : conePoint B 1 0 ≫ q = conePoint B' 1 0 := by
  refine Atom.hom_ext fun v => ?_
  obtain rfl : v = default := Subsingleton.elim _ _
  have htop : q (cone B 1).top = (cone B' 1).top :=
    hq.apply_top
  have h := (Atom.isMap q).image_boundary (cone B 1).top 0 true
  rw [htop, boundary_closure_top_zero_true_cone_one, boundary_closure_top_zero_true_cone_one,
    Set.image_singleton] at h
  exact Set.singleton_eq_singleton_iff.1 h

@[reassoc] theorem coneIncl_comp_coneAssoc_comp_coneHom (B : Atom) :
    coneIncl (cone B 1) 1 ≫ (coneAssoc B 1 1).hom ≫
      coneHom B (OrderHom.const _ (0 : Fin 1)) = 𝟙 (cone B 1) := by
  rw [coneIncl_comp_coneAssoc_assoc, coneHom_comp, ← coneHom_id]
  congr 1
  exact OrderHom.ext _ _ (funext fun i => Subsingleton.elim _ _)

theorem coneMap_coneAssoc_comp_coneHom_comp (B : Atom) :
    coneMap ((coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1))) 1 ≫
        (coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1)) =
      (coneAssoc (cone B 1) 1 1).hom ≫
        coneHom (cone B 1) (OrderHom.const _ (0 : Fin 1)) ≫
          (coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1)) := by
  refine cone_hom_ext (B := cone (cone B 1) 1) (r := 1) (F := B) (s := 1) (fun _ => 0)
    (fun i => by simp) (fun i => by simp) ?_
  have h : (OrderHom.const (Fin (1 + 1)) (0 : Fin 1)).comp ⟨Fin.castAdd 1, fun _ _ h => h⟩ =
      OrderHom.id := OrderHom.ext _ _ (funext fun i => Subsingleton.elim _ _)
  rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc_comp_coneHom, Category.comp_id,
    coneIncl_comp_coneAssoc_assoc, coneHom_comp_assoc, h, coneHom_id, Category.id_comp]

theorem coneMap_comp_coneAssoc_comp_coneHom_of_isCollapseHom {B B' : Atom}
    (q : cone B 1 ⟶ cone B' 1) (hq : IsCollapseHom q) :
    coneMap q 1 ≫ (coneAssoc B' 1 1).hom ≫ coneHom B' (OrderHom.const _ (0 : Fin 1)) =
      ((coneAssoc B 1 1).hom ≫ coneHom B (OrderHom.const _ (0 : Fin 1))) ≫ q := by
  refine cone_hom_ext (B := cone B 1) (r := 1) (F := B') (s := 1) (fun _ => 0)
    (fun i => by simp) (fun i => ?_) ?_
  · rw [Category.assoc, conePoint_comp_coneAssoc_assoc, conePoint_comp_coneHom_assoc]
    exact conePoint_comp_eq_of_isCollapseHom q hq
  · rw [coneIncl_comp_coneMap_assoc, coneIncl_comp_coneAssoc_comp_coneHom, Category.comp_id,
      Category.assoc, coneIncl_comp_coneAssoc_comp_coneHom_assoc]

theorem exists_coneMap_comp_eq {B C : Atom} {n r : ℕ}
    (hC : (IsCore C ∧ 0 < C.dimension) ∨ C = atomPoint) (ρ : cone B n ⟶ cone C r)
    (hρ : IsCollapseHom ρ) :
    ∃ (K : ℕ) (hK : K ≤ r) (Q : B ⟶ cone C K) (ℓ : cone (cone C K) n ⟶ cone C r),
      IsCollapseHom Q ∧ coneIncl (cone C K) n ≫ ℓ = coneHom C (Fin.castLEOrderEmb hK).toOrderHom ∧
        coneMap Q n ≫ ℓ = ρ := by
  rcases hC with ⟨hC, hd⟩ | rfl
  · obtain ⟨k, hk, q₀, σ, hq₀, -, hσ, rfl⟩ := exists_coneHom_factorization hC hd ρ hρ
    refine ⟨k, hk, q₀, (coneAssoc C k n).hom ≫ coneHom C σ, hq₀, ?_, rfl⟩
    rw [coneIncl_comp_coneAssoc_assoc, coneHom_comp]
    congr 1
    exact OrderHom.ext _ _ (funext hσ)
  · obtain ⟨k, hk, q₀, σ, hq₀, -, hσ, heq⟩ := exists_simplexHom_factorization
      (ρ ≫ (coneAtomPointIso r).hom) (collapses.comp_mem _ _ hρ (isCollapseHom_of_iso _))
    refine ⟨k, hk, q₀, (coneAssoc atomPoint k n).hom ≫ (coneAtomPointIso (k + n)).hom ≫
      simplexHom σ ≫ (coneAtomPointIso r).inv, hq₀, ?_, ?_⟩
    · rw [← cancel_mono (coneAtomPointIso r).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [coneIncl_comp_coneAssoc_assoc]
      refine hom_ext_atomSimplex fun v hv => atomSimplexVertices_injective r ?_
      rcases exists_eq_of_grade_eq_zero_cone hv with ⟨b, rfl⟩ | ⟨i, rfl⟩
      · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          coneIncl_comp_coneHom_assoc, coneIncl_comp_coneHom_assoc,
          ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
          atomSimplexVertices_simplexHom, atomSimplexVertices_coneAtomPointIso_coneIncl,
          atomSimplexVertices_coneAtomPointIso_coneIncl, Finset.image_singleton]
        exact congrArg _ (hσ 0)
      · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          conePoint_comp_coneHom_assoc, conePoint_comp_coneHom_assoc,
          ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
          atomSimplexVertices_simplexHom, atomSimplexVertices_coneAtomPointIso_conePoint,
          atomSimplexVertices_coneAtomPointIso_conePoint, Finset.image_singleton]
        congr 1
        have := hσ i.succ
        refine (congrArg σ (Fin.ext ?_)).trans (this.trans (Fin.ext ?_))
        · simp only [Fin.val_succ, Fin.val_castLE]
          rfl
        · simp
    · rw [← cancel_mono (coneAtomPointIso r).hom, heq]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Atoms.Shape
