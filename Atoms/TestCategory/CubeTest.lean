import Atoms.TestCategory.PrecylinderCriterion

open CategoryTheory Limits

namespace Atoms.TestCategory

universe u

inductive CubeCoord (m : ℕ) : Type
  | const (b : Bool)
  | proj (i : Fin m)
  deriving DecidableEq

namespace CubeCoord

def IsOrdered {m n : ℕ} (f : Fin n → CubeCoord m) : Prop :=
  ∀ ⦃j₁ j₂ : Fin n⦄ ⦃i₁ i₂ : Fin m⦄, j₁ < j₂ → f j₁ = .proj i₁ → f j₂ = .proj i₂ → i₁ < i₂

def subst {l m : ℕ} (c : CubeCoord m) (f : Fin m → CubeCoord l) : CubeCoord l :=
  match c with
  | const b => const b
  | proj i => f i

def eval {m : ℕ} (c : CubeCoord m) (x : Fin m → Bool) : Bool :=
  match c with
  | const b => b
  | proj i => x i

def succ {m : ℕ} (c : CubeCoord m) : CubeCoord (m + 1) :=
  match c with
  | const b => const b
  | proj i => proj i.succ

@[simp]
theorem const_subst {l m : ℕ} (b : Bool) (f : Fin m → CubeCoord l) : (const b).subst f = const b :=
  rfl

@[simp]
theorem proj_subst {l m : ℕ} (i : Fin m) (f : Fin m → CubeCoord l) : (proj i).subst f = f i :=
  rfl

@[simp]
theorem const_eval {m : ℕ} (b : Bool) (x : Fin m → Bool) : (const b).eval x = b :=
  rfl

@[simp]
theorem proj_eval {m : ℕ} (i : Fin m) (x : Fin m → Bool) : (proj i).eval x = x i :=
  rfl

@[simp]
theorem const_succ {m : ℕ} (b : Bool) : (const b : CubeCoord m).succ = const b :=
  rfl

@[simp]
theorem proj_succ {m : ℕ} (i : Fin m) : (proj i).succ = proj i.succ :=
  rfl

@[simp]
theorem subst_proj {m : ℕ} (c : CubeCoord m) : c.subst proj = c := by
  cases c <;> rfl

theorem subst_subst {k l m : ℕ} (c : CubeCoord m) (f : Fin m → CubeCoord l)
    (g : Fin l → CubeCoord k) : (c.subst f).subst g = c.subst fun i => (f i).subst g := by
  cases c <;> rfl

@[simp]
theorem succ_subst_cons {l m : ℕ} (c : CubeCoord m) (d : CubeCoord l) (f : Fin m → CubeCoord l) :
    c.succ.subst (Fin.cons d f) = c.subst f := by
  cases c <;> rfl

theorem subst_eval {l m : ℕ} (c : CubeCoord m) (f : Fin m → CubeCoord l) (x : Fin l → Bool) :
    (c.subst f).eval x = c.eval fun i => (f i).eval x := by
  cases c <;> rfl

theorem exists_of_subst_eq_proj {l m : ℕ} {c : CubeCoord m} {f : Fin m → CubeCoord l} {i : Fin l}
    (h : c.subst f = proj i) : ∃ k, c = proj k ∧ f k = proj i := by
  cases c with
  | const b => cases h
  | proj k => exact ⟨k, rfl, h⟩

theorem exists_of_succ_eq_proj {m : ℕ} {c : CubeCoord m} {i : Fin (m + 1)} (h : c.succ = proj i) :
    ∃ k, c = proj k ∧ k.succ = i := by
  cases c with
  | const b => cases h
  | proj k => exact ⟨k, rfl, proj.inj h⟩

theorem IsOrdered.subst {l m n : ℕ} {f : Fin m → CubeCoord l} {g : Fin n → CubeCoord m}
    (hf : IsOrdered f) (hg : IsOrdered g) : IsOrdered fun j => (g j).subst f := by
  intro j₁ j₂ i₁ i₂ hj h₁ h₂
  obtain ⟨k₁, hk₁, hf₁⟩ := exists_of_subst_eq_proj h₁
  obtain ⟨k₂, hk₂, hf₂⟩ := exists_of_subst_eq_proj h₂
  exact hf (hg hj hk₁ hk₂) hf₁ hf₂

theorem isOrdered_proj (m : ℕ) : IsOrdered (proj : Fin m → CubeCoord m) :=
  fun _ _ _ _ hj h₁ h₂ => by
    cases h₁
    cases h₂
    exact hj

theorem isOrdered_cons {m n : ℕ} {d : CubeCoord (m + 1)} (hd : ∀ i, d = proj i → i = 0)
    {f : Fin n → CubeCoord m} (hf : IsOrdered f) :
    IsOrdered (Fin.cons d fun j => (f j).succ : Fin (n + 1) → CubeCoord (m + 1)) := by
  intro j₁ j₂ i₁ i₂ hj h₁ h₂
  induction j₂ using Fin.cases with
  | zero => exact absurd hj (Fin.not_lt_zero _)
  | succ j₂ =>
    rw [Fin.cons_succ] at h₂
    obtain ⟨k₂, hk₂, rfl⟩ := exists_of_succ_eq_proj h₂
    induction j₁ using Fin.cases with
    | zero =>
      rw [hd i₁ h₁]
      exact Fin.succ_pos _
    | succ j₁ =>
      rw [Fin.cons_succ] at h₁
      obtain ⟨k₁, hk₁, rfl⟩ := exists_of_succ_eq_proj h₁
      exact Fin.succ_lt_succ_iff.2 (hf (Fin.succ_lt_succ_iff.1 hj) hk₁ hk₂)

theorem isOrdered_cons_const {m n : ℕ} (b : Bool) {f : Fin n → CubeCoord m} (hf : IsOrdered f) :
    IsOrdered (Fin.cons (const b) f : Fin (n + 1) → CubeCoord m) := by
  intro j₁ j₂ i₁ i₂ hj h₁ h₂
  induction j₂ using Fin.cases with
  | zero => exact absurd hj (Fin.not_lt_zero _)
  | succ j₂ =>
    induction j₁ using Fin.cases with
    | zero => cases h₁
    | succ j₁ => exact hf (Fin.succ_lt_succ_iff.1 hj) h₁ h₂

theorem eval_injective {m : ℕ} : Function.Injective (eval (m := m)) := by
  intro c d h
  cases c with
  | const b =>
    cases d with
    | const b' => exact congrArg const (congrFun h fun _ => false)
    | proj i => exact absurd (congrFun h fun _ => !b) (by simp)
  | proj i =>
    cases d with
    | const b => exact absurd (congrFun h fun _ => !b) (by simp)
    | proj i' =>
      have := congrFun h fun k => decide (k = i)
      simp only [proj_eval, decide_true] at this
      rw [of_decide_eq_true this.symm]

end CubeCoord

def Cube : Type u := ULift.{u} ℕ

namespace Cube

@[ext]
structure Hom (m n : Cube.{u}) : Type u where
  coord : Fin n.down → CubeCoord m.down
  ordered : CubeCoord.IsOrdered coord

instance : SmallCategory Cube.{u} where
  Hom := Hom
  id _ := ⟨CubeCoord.proj, CubeCoord.isOrdered_proj _⟩
  comp f g := ⟨fun j => (g.coord j).subst f.coord, f.ordered.subst g.ordered⟩
  id_comp _ := Hom.ext (funext fun _ => CubeCoord.subst_proj _)
  comp_id _ := rfl
  assoc _ _ h := Hom.ext (funext fun j => (CubeCoord.subst_subst (h.coord j) _ _).symm)

@[ext]
theorem hom_ext {m n : Cube.{u}} {f g : m ⟶ n} (h : ∀ j, f.coord j = g.coord j) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem id_coord (m : Cube.{u}) (j : Fin m.down) : Hom.coord (𝟙 m) j = .proj j :=
  rfl

@[simp]
theorem comp_coord {l m n : Cube.{u}} (f : l ⟶ m) (g : m ⟶ n) (j : Fin n.down) :
    (f ≫ g).coord j = (g.coord j).subst f.coord :=
  rfl

def toFun {m n : Cube.{u}} (f : m ⟶ n) : (Fin m.down → Bool) → (Fin n.down → Bool) :=
  fun x j => (f.coord j).eval x

@[simp]
theorem toFun_apply {m n : Cube.{u}} (f : m ⟶ n) (x : Fin m.down → Bool) (j : Fin n.down) :
    Cube.toFun f x j = (f.coord j).eval x :=
  rfl

@[simp]
theorem toFun_id (m : Cube.{u}) : Cube.toFun (𝟙 m) = id :=
  rfl

theorem toFun_injective {m n : Cube.{u}} : Function.Injective (Cube.toFun (m := m) (n := n)) :=
  fun _ _ h => hom_ext fun j => CubeCoord.eval_injective (funext fun x => congrFun (congrFun h x) j)

theorem toFun_comp {l m n : Cube.{u}} (f : l ⟶ m) (g : m ⟶ n) :
    Cube.toFun (f ≫ g) = Cube.toFun g ∘ Cube.toFun f :=
  funext fun x => funext fun j => CubeCoord.subst_eval (g.coord j) f.coord x

theorem toFun_monotone {m n : Cube.{u}} (f : m ⟶ n) : Monotone (Cube.toFun f) :=
  fun x y h j => by
    cases hc : f.coord j with
    | const b => simp [Cube.toFun, hc]
    | proj k => simpa [Cube.toFun, hc] using h k

def isTerminalZero : IsTerminal (C := Cube.{u}) (ULift.up 0) :=
  IsTerminal.ofUniqueHom (fun _ => ⟨Fin.elim0, fun j => Fin.elim0 j⟩)
    (fun _ _ => hom_ext fun j => Fin.elim0 j)

instance hasTerminal : HasTerminal Cube.{u} :=
  isTerminalZero.hasTerminal

abbrev succ (n : Cube.{u}) : Cube.{u} :=
  ⟨n.down + 1⟩

def succMap {m n : Cube.{u}} (f : m ⟶ n) : succ m ⟶ succ n :=
  ⟨Fin.cons (.proj 0) fun j => (f.coord j).succ,
    CubeCoord.isOrdered_cons (fun _ h => (CubeCoord.proj.inj h).symm) f.ordered⟩

@[simp]
theorem succMap_coord_zero {m n : Cube.{u}} (f : m ⟶ n) :
    (succMap f).coord 0 = .proj 0 :=
  rfl

@[simp]
theorem succMap_coord_succ {m n : Cube.{u}} (f : m ⟶ n) (j : Fin n.down) :
    (succMap f).coord j.succ = (f.coord j).succ :=
  rfl

def face (ε : Bool) (n : Cube.{u}) : n ⟶ succ n :=
  ⟨Fin.cons (.const ε) .proj,
    CubeCoord.isOrdered_cons_const ε (CubeCoord.isOrdered_proj n.down)⟩

@[simp]
theorem face_coord_zero (ε : Bool) (n : Cube.{u}) : (face ε n).coord 0 = .const ε :=
  rfl

@[simp]
theorem face_coord_succ (ε : Bool) (n : Cube.{u}) (j : Fin n.down) :
    (face ε n).coord j.succ = .proj j :=
  rfl

def degeneracy (n : Cube.{u}) : succ n ⟶ n :=
  ⟨fun j => .proj j.succ, fun _ _ _ _ hj h₁ h₂ => by
    cases h₁
    cases h₂
    exact Fin.succ_lt_succ_iff.2 hj⟩

@[simp]
theorem degeneracy_coord (n : Cube.{u}) (j : Fin n.down) :
    (degeneracy n).coord j = .proj j.succ :=
  rfl

def succFunctor : Cube.{u} ⥤ Cube.{u} where
  obj := succ
  map := succMap
  map_id n := hom_ext fun j => by
    induction j using Fin.cases <;> simp
  map_comp f g := hom_ext fun j => by
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      cases hg : g.coord j <;> simp [hg, succMap, CubeCoord.succ]

def precylinder : FunctorialPrecylinder Cube.{u} where
  I := succFunctor
  ι ε :=
    { app := face ε
      naturality _ _ f := hom_ext fun j => by
        induction j using Fin.cases with
        | zero => rfl
        | succ j =>
          cases hf : f.coord j <;> simp [hf, succFunctor, succMap, face] }

def augmentation : Cube.precylinder.{u}.Augmentation where
  σ := degeneracy
  ι_σ _ _ := hom_ext fun _ => rfl

theorem eq_comp_face_of_coord_zero {a b : Cube.{u}} (f : b ⟶ succ a)
    (hf : f.coord 0 = .const false) : f = (f ≫ degeneracy a) ≫ face false a :=
  hom_ext fun j => by
    induction j using Fin.cases with
    | zero => exact hf
    | succ j => rfl

theorem isSeparating_precylinder : Cube.precylinder.{u}.IsSeparating where
  mono a := mono_of_mono_fac (augmentation.ι_σ false a)
  ne {a b} f g h := by
    change f ≫ face true a = g ≫ face false a at h
    have := congrArg (fun k : b ⟶ succ a => k.coord 0) h
    simp at this
  map_ne {a a' b} α f hf g h := by
    change f ≫ succMap α = g ≫ face false a' at h
    have := congrArg (fun k : b ⟶ succ a' => k.coord 0) h
    simp only [comp_coord, face_coord_zero, CubeCoord.const_subst] at this
    exact hf _ (eq_comp_face_of_coord_zero f this)

end Cube

namespace BasicLocalizer

instance isTest_cube (𝒲 : BasicLocalizer.{u}) : 𝒲.IsTest Cube.{u} :=
  𝒲.isTest_of_isSeparating Cube.precylinder Cube.augmentation Cube.isSeparating_precylinder

end BasicLocalizer

end Atoms.TestCategory
