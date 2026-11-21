import Atoms.Molecule.Construction.GrayCylinder
import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Molecule.Construction.SimplexMaps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

open SuspCarrier

def cubeCoface : (n i : ℕ) → i ≤ n → Bool → (cube.{u} n ⟶ cube.{u} (n + 1))
  | n, 0, _, α => cylEndpoint α (cube n)
  | 0, i + 1, h, _ => absurd h (Nat.not_succ_le_zero i)
  | n + 1, i + 1, h, α =>
    grayProductMap (𝟙 (globe 1)) (cubeCoface n i (Nat.le_of_succ_le_succ h) α)
termination_by structural _ i => i

@[simp] theorem cubeCoface_zero (n : ℕ) (h : 0 ≤ n) (α : Bool) (x : cube.{u} n) :
    cubeCoface n 0 h α x = (pole α, x) :=
  rfl

@[simp] theorem cubeCoface_succ (n i : ℕ) (h : i + 1 ≤ n + 1) (α : Bool)
    (x : cube.{u} (n + 1)) :
    cubeCoface (n + 1) (i + 1) h α x = (x.1, cubeCoface n i (Nat.le_of_succ_le_succ h) α x.2) :=
  rfl

instance (n i : ℕ) (h : i ≤ n) (α : Bool) : IsInclusion (cubeCoface.{u} n i h α) := by
  induction i generalizing n with
  | zero => exact inferInstanceAs (IsInclusion (cylEndpoint α (cube n)))
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := ih n (Nat.le_of_succ_le_succ h)
    exact inferInstanceAs (IsInclusion (grayProductMap (𝟙 (globe 1)) (cubeCoface n i _ α)))

def cubeCodegeneracy : (n i : ℕ) → i ≤ n → cube.{u} (n + 1) → cube.{u} n
  | _, 0, _ => Prod.snd
  | 0, i + 1, h => absurd h (Nat.not_succ_le_zero i)
  | n + 1, i + 1, h => fun p => (p.1, cubeCodegeneracy n i (Nat.le_of_succ_le_succ h) p.2)
termination_by structural _ i => i

@[simp] theorem cubeCodegeneracy_zero (n : ℕ) (h : 0 ≤ n) (x : cube.{u} (n + 1)) :
    cubeCodegeneracy n 0 h x = x.2 :=
  rfl

@[simp] theorem cubeCodegeneracy_succ (n i : ℕ) (h : i + 1 ≤ n + 1) (x : cube.{u} (n + 2)) :
    cubeCodegeneracy (n + 1) (i + 1) h x =
      (x.1, cubeCodegeneracy n i (Nat.le_of_succ_le_succ h) x.2) :=
  rfl

theorem isMap_cubeCodegeneracy (n i : ℕ) (h : i ≤ n) : IsMap (cubeCodegeneracy.{u} n i h) := by
  induction i generalizing n with
  | zero => exact isMap_snd_grayProduct_globe_one (isRDC_cube n)
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact isMap_prod_right_of_isMap isRDC_globe_one (isRDC_cube (n + 1)) (isRDC_cube n)
      (ih n (Nat.le_of_succ_le_succ h))

theorem surjective_cubeCodegeneracy (n i : ℕ) (h : i ≤ n) :
    Function.Surjective (cubeCodegeneracy.{u} n i h) := by
  induction i generalizing n with
  | zero => exact fun x => ⟨(pole false, x), rfl⟩
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rintro ⟨a, x⟩
    obtain ⟨y, rfl⟩ := ih n (Nat.le_of_succ_le_succ h) x
    exact ⟨(a, y), rfl⟩

theorem cubeCodegeneracy_cubeCoface (n i : ℕ) (h : i ≤ n) (α : Bool) (x : cube.{u} n) :
    cubeCodegeneracy n i h (cubeCoface n i h α x) = x := by
  induction i generalizing n with
  | zero => rfl
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Prod.ext rfl (ih n (Nat.le_of_succ_le_succ h) x.2)

def globeOneConnection (α : Bool) : grayProduct (globe.{u} 1) (globe.{u} 1) → globe.{u} 1
  | (pole β, c) => if β = α then pole α else c
  | (susp x, pole β) => if β = α then pole α else susp x
  | (susp x, susp _) => susp x

@[simp] theorem globeOneConnection_pole_left (α : Bool) (c : globe.{u} 1) :
    globeOneConnection α (pole α, c) = pole α :=
  if_pos rfl

@[simp] theorem globeOneConnection_pole_right (α : Bool) (c : globe.{u} 1) :
    globeOneConnection α (c, pole α) = pole α := by
  rcases c with β | x
  · exact ite_self _
  · exact if_pos rfl

@[simp] theorem globeOneConnection_pole_not_left (α : Bool) (c : globe.{u} 1) :
    globeOneConnection α (pole (!α), c) = c :=
  if_neg (Bool.not_ne_self α)

@[simp] theorem globeOneConnection_pole_not_right (α : Bool) (c : globe.{u} 1) :
    globeOneConnection α (c, pole (!α)) = c := by
  rcases c with β | x
  · cases α <;> cases β <;> rfl
  · exact if_neg (Bool.not_ne_self α)

@[simp] theorem globeOneConnection_top (α : Bool) : globeOneConnection.{u} α (⊤, ⊤) = ⊤ :=
  rfl

private theorem globeOneConnection_pole_pole (α β : Bool) :
    globeOneConnection.{u} α (pole β, pole β) = pole β := by
  cases α <;> cases β <;> rfl

private theorem isRDC_square : IsRDC (grayProduct (globe.{u} 1) (globe.{u} 1)) :=
  isRDC_of_isMolecule (isAtom_grayProduct (isAtom_globe 1) (isAtom_globe 1)).1

private theorem exists_isMap_eqOn_Iic (α : Bool) {x : grayProduct (globe.{u} 1) (globe.{u} 1)}
    (hx : x ≠ (⊤, ⊤)) :
    ∃ g : grayProduct (globe.{u} 1) (globe.{u} 1) → globe.{u} 1, IsMap g ∧
      EqOn (globeOneConnection α) g (Iic x) := by
  have hconst :=
    (isMap_constPoint isRDC_square).comp (isMap_of_isInclusion (suspension.poleIncl (globe 0) α))
  have hfst :=
    (isMap_prod_right_of_isMap isRDC_globe_one isRDC_globe_one
      isRDC_point (isMap_constPoint isRDC_globe_one)).comp
      (isMap_of_isInclusion (grayProductRightUnitor (globe.{u} 1)).hom)
  have hsnd := isMap_snd_grayProduct_globe_one (isRDC_globe_one.{u})
  have hside (β : Bool) : β = α ∨ β = !α := by cases α <;> cases β <;> simp
  rcases x with ⟨β | ⟨⟨⟩⟩, b⟩
  · rcases hside β with rfl | rfl
    · refine ⟨_, hconst, fun y hy => ?_⟩
      obtain ⟨y₁, y₂⟩ := y
      obtain rfl := (isMin_pole β).eq_of_le hy.1
      exact globeOneConnection_pole_left _ _
    · refine ⟨_, hsnd, fun y hy => ?_⟩
      obtain ⟨y₁, y₂⟩ := y
      obtain rfl := (isMin_pole _).eq_of_le hy.1
      exact globeOneConnection_pole_not_left _ _
  · rcases b with β | ⟨⟨⟩⟩
    · rcases hside β with rfl | rfl
      · refine ⟨_, hconst, fun y hy => ?_⟩
        obtain ⟨y₁, y₂⟩ := y
        obtain rfl := (isMin_pole β).eq_of_le hy.2
        exact globeOneConnection_pole_right _ _
      · refine ⟨_, hfst, fun y hy => ?_⟩
        obtain ⟨y₁, y₂⟩ := y
        obtain rfl := (isMin_pole _).eq_of_le hy.2
        exact globeOneConnection_pole_not_right _ _
    · exact (hx rfl).elim

private theorem fibration_globeOneConnection (α : Bool) :
    Relation.Fibration (· ≤ ·) (· ≤ ·) (globeOneConnection.{u} α) := by
  intro x y hy
  by_cases hx : x = (⊤, ⊤)
  · subst hx
    rcases y with β | ⟨⟨⟩⟩
    · exact ⟨(pole β, pole β), Prod.mk_le_mk.2 ⟨le_top, le_top⟩, globeOneConnection_pole_pole α β⟩
    · exact ⟨(⊤, ⊤), le_rfl, rfl⟩
  · obtain ⟨g, hg, he⟩ := exists_isMap_eqOn_Iic α hx
    rw [he (mem_Iic.2 le_rfl)] at hy
    obtain ⟨x', hx', rfl⟩ := hg.fibration hy
    exact ⟨x', hx', he hx'⟩

private theorem monotone_globeOneConnection (α : Bool) : Monotone (globeOneConnection.{u} α) := by
  intro a x hax
  by_cases hx : x = (⊤, ⊤)
  · subst hx
    exact le_top
  · obtain ⟨g, hg, he⟩ := exists_isMap_eqOn_Iic α hx
    rw [he (mem_Iic.2 le_rfl), he (mem_Iic.2 hax)]
    exact hg.monotone hax

private theorem mem_boundary_zero_globe_one {b : globe.{u} 1} {β : Bool} :
    b ∈ (globe.{u} 1).boundary (.Iic ⊤) 0 β ↔ b = pole β := by
  rw [LowerSet.Iic_top, boundary_zero_globe_one, LowerSet.mem_Iic_iff]
  exact ⟨(isMin_pole β).eq_of_le, fun h => h ▸ le_rfl⟩

private theorem mem_boundary_pos_globe_one (b : globe.{u} 1) {k : ℕ} (hk : 0 < k) (β : Bool) :
    b ∈ (globe.{u} 1).boundary (.Iic ⊤) k β := by
  rw [boundary_eq_self (by rw [LowerSet.krullDim_Iic, grade_top_globe]; exact_mod_cast hk) β]
  exact le_top (a := b)

private theorem mem_boundary_zero_square {β : Bool} {p : grayProduct (globe.{u} 1) (globe.{u} 1)} :
    p ∈ (grayProduct (globe.{u} 1) (globe.{u} 1)).boundary (.Iic (⊤, ⊤)) 0 β ↔
      p = (pole β, pole β) := by
  obtain ⟨b, c⟩ := p
  rw [mem_boundary_Iic_grayProduct isRDC_globe_one isRDC_globe_one]
  constructor
  · rintro ⟨k, hk, hb, hc⟩
    obtain rfl := Nat.le_zero.1 hk
    rw [Nat.sub_zero, Nat.bodd_zero, Bool.false_xor] at hc
    rw [mem_boundary_zero_globe_one.1 hb, mem_boundary_zero_globe_one.1 hc]
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨0, le_rfl, mem_boundary_zero_globe_one.2 rfl, ?_⟩
    rw [Nat.sub_zero, Nat.bodd_zero, Bool.false_xor]
    exact mem_boundary_zero_globe_one.2 rfl

private theorem mem_boundary_one_square {β : Bool} {b c : globe.{u} 1} :
    ((b, c) : grayProduct (globe.{u} 1) (globe.{u} 1)) ∈
        (grayProduct (globe.{u} 1) (globe.{u} 1)).boundary (.Iic (⊤, ⊤)) 1 β ↔
      b = pole β ∨ c = pole (!β) := by
  rw [mem_boundary_Iic_grayProduct isRDC_globe_one isRDC_globe_one]
  constructor
  · rintro ⟨k, hk, hb, hc⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · exact .inl (mem_boundary_zero_globe_one.1 hb)
    · rw [Nat.sub_self, Nat.bodd_one, Bool.true_xor] at hc
      exact .inr (mem_boundary_zero_globe_one.1 hc)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_le_one, mem_boundary_zero_globe_one.2 rfl,
        mem_boundary_pos_globe_one c one_pos _⟩
    · refine ⟨1, le_rfl, mem_boundary_pos_globe_one b one_pos _, ?_⟩
      rw [Nat.sub_self, Nat.bodd_one, Bool.true_xor]
      exact mem_boundary_zero_globe_one.2 rfl

private theorem reflTransGen_of_le {P Q : OGP.{u}} {f : P → Q} (hf : Monotone f) {S : Set P}
    {w : Q} {a b : P} (ha : a ∈ S) (hb : b ∈ S) (hw : w ≤ f a) (hab : a ≤ b) :
    Relation.ReflTransGen (fun c d => c ∈ S ∩ f ⁻¹' Ici w ∧ d ∈ S ∩ f ⁻¹' Ici w ∧
        (c ≤ d ∨ d ≤ c)) a b ∧
      Relation.ReflTransGen (fun c d => c ∈ S ∩ f ⁻¹' Ici w ∧ d ∈ S ∩ f ⁻¹' Ici w ∧
        (c ≤ d ∨ d ≤ c)) b a :=
  have ha' : a ∈ S ∩ f ⁻¹' Ici w := ⟨ha, hw⟩
  have hb' : b ∈ S ∩ f ⁻¹' Ici w := ⟨hb, hw.trans (hf hab)⟩
  ⟨.single ⟨ha', hb', .inl hab⟩, .single ⟨hb', ha', .inr hab⟩⟩

private theorem finalOn_globeOneConnection_one (α β : Bool) :
    FinalOn (globeOneConnection.{u} α)
      ((grayProduct (globe.{u} 1) (globe.{u} 1)).boundary (.Iic (⊤, ⊤)) 1 β)
      ((globe.{u} 1).boundary (.Iic ⊤) 1 β) := by
  have hside (γ : Bool) : γ = α ∨ γ = !α := by cases α <;> cases γ <;> simp
  have hmono := monotone_globeOneConnection.{u} α
  refine finalOn_of_fibration (IsUpperSet.isClosedMap_iff_fibration.2
    (fibration_globeOneConnection α)) (Set.eq_of_subset_of_subset
      (fun w _ => mem_boundary_pos_globe_one w one_pos β) fun w _ => ?_) ?_
  · rcases w with δ | ⟨⟨⟩⟩
    · refine ⟨(pole δ, pole δ), mem_boundary_one_square.2 ?_, globeOneConnection_pole_pole α δ⟩
      cases β <;> cases δ <;> simp
    · rcases hside β with rfl | rfl
      · exact ⟨(⊤, pole (!β)), mem_boundary_one_square.2 (.inr rfl),
          globeOneConnection_pole_not_right _ _⟩
      · exact ⟨(pole (!α), ⊤), mem_boundary_one_square.2 (.inl rfl),
          globeOneConnection_pole_not_left _ _⟩
  · rintro ⟨y₁, y₂⟩ hy ⟨z₁, z₂⟩ hz h
    have hL := mem_boundary_one_square.{u} (β := β) (b := pole β) (c := ⊤) |>.2 (.inl rfl)
    have hB := mem_boundary_one_square.{u} (β := β) (b := ⊤) (c := pole (!β)) |>.2 (.inr rfl)
    have hc := mem_boundary_one_square.{u} (β := β) (b := pole β) (c := pole (!β)) |>.2 (.inl rfl)
    have hcL : ((pole β, pole (!β)) : grayProduct (globe.{u} 1) (globe.{u} 1)) ≤ (pole β, ⊤) :=
      Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩
    have hcB : ((pole β, pole (!β)) : grayProduct (globe.{u} 1) (globe.{u} 1)) ≤ (⊤, pole (!β)) :=
      Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩
    have hγc : globeOneConnection.{u} α (pole β, pole (!β)) = pole α := by
      rcases hside β with rfl | rfl
      · exact globeOneConnection_pole_left _ _
      · rw [Bool.not_not]
        exact globeOneConnection_pole_right _ _
    rcases mem_boundary_one_square.1 hy with rfl | rfl <;>
      rcases mem_boundary_one_square.1 hz with rfl | rfl
    · exact (reflTransGen_of_le hmono hy hL le_rfl (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩)).1.trans
        (reflTransGen_of_le hmono hz hL h.le (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩)).2
    · have hγy : globeOneConnection α (pole β, y₂) = pole α := by
        rcases hside β with rfl | rfl
        · exact globeOneConnection_pole_left _ _
        · rw [h, Bool.not_not]
          exact globeOneConnection_pole_right _ _
      exact (((reflTransGen_of_le hmono hy hL le_rfl (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩)).1.trans
        (reflTransGen_of_le hmono hc hL (hγy.trans hγc.symm).le hcL).2).trans
        (reflTransGen_of_le hmono hc hB (hγy.trans hγc.symm).le hcB).1).trans
        (reflTransGen_of_le hmono hz hB h.le (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩)).2
    · have hγy : globeOneConnection α (y₁, pole (!β)) = pole α := by
        rcases hside β with rfl | rfl
        · rw [h]
          exact globeOneConnection_pole_left _ _
        · rw [Bool.not_not]
          exact globeOneConnection_pole_right _ _
      exact (((reflTransGen_of_le hmono hy hB le_rfl (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩)).1.trans
        (reflTransGen_of_le hmono hc hB (hγy.trans hγc.symm).le hcB).2).trans
        (reflTransGen_of_le hmono hc hL (hγy.trans hγc.symm).le hcL).1).trans
        (reflTransGen_of_le hmono hz hL h.le (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩)).2
    · exact (reflTransGen_of_le hmono hy hB le_rfl (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩)).1.trans
        (reflTransGen_of_le hmono hz hB h.le (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩)).2

private theorem finalOn_globeOneConnection_top (α : Bool) (n : ℕ) (β : Bool) :
    FinalOn (globeOneConnection.{u} α)
      ((grayProduct (globe.{u} 1) (globe.{u} 1)).boundary (.Iic (⊤, ⊤)) n β)
      ((globe.{u} 1).boundary (.Iic (globeOneConnection α (⊤, ⊤))) n β) := by
  rw [globeOneConnection_top]
  rcases n with _ | _ | n
  · refine finalOn_of_fibration (IsUpperSet.isClosedMap_iff_fibration.2
      (fibration_globeOneConnection α)) (Set.ext fun w => ?_) fun y hy z hz _ => ?_
    · rw [SetLike.mem_coe, mem_boundary_zero_globe_one]
      refine ⟨?_, fun hw => ⟨(pole β, pole β), mem_boundary_zero_square.2 rfl,
        (globeOneConnection_pole_pole α β).trans hw.symm⟩⟩
      rintro ⟨p, hp, rfl⟩
      rw [mem_boundary_zero_square.1 hp]
      exact globeOneConnection_pole_pole α β
    · rw [mem_boundary_zero_square.1 hy, mem_boundary_zero_square.1 hz]
  · exact finalOn_globeOneConnection_one α β
  · rw [boundary_eq_self (by
        rw [LowerSet.krullDim_Iic, Prod.grade_eq_add, grade_top_globe]
        exact_mod_cast (by omega : 1 + 1 ≤ n + 2)) β,
      boundary_eq_self (by
        rw [LowerSet.krullDim_Iic, grade_top_globe]
        exact_mod_cast (by omega : 1 ≤ n + 2)) β]
    exact finalOn_Iic (monotone_globeOneConnection α) (⊤, ⊤)

theorem isMap_globeOneConnection (α : Bool) : IsMap (globeOneConnection.{u} α) := by
  refine ⟨IsUpperSet.isClosedMap_iff_fibration.2 (fibration_globeOneConnection α),
    fun x n β => ?_⟩
  by_cases hx : x = (⊤, ⊤)
  · subst hx
    exact finalOn_globeOneConnection_top α n β
  · obtain ⟨g, hg, he⟩ := exists_isMap_eqOn_Iic α hx
    have hfin := hg.finalOn x n β
    rw [← he (mem_Iic.2 le_rfl)] at hfin
    have he' : EqOn (globeOneConnection α) g
        ((grayProduct (globe.{u} 1) (globe.{u} 1)).boundary (.Iic x) n β) :=
      fun z hz => he (boundary_le _ _ _ hz)
    exact hfin.congr he'.symm

def cubeConnection : (n i : ℕ) → i ≤ n → Bool → cube.{u} (n + 2) → cube.{u} (n + 1)
  | _, 0, _, α => fun p => (globeOneConnection α (p.1, p.2.1), p.2.2)
  | 0, i + 1, h, _ => absurd h (Nat.not_succ_le_zero i)
  | n + 1, i + 1, h, α => fun p => (p.1, cubeConnection n i (Nat.le_of_succ_le_succ h) α p.2)
termination_by structural _ i => i

@[simp] theorem cubeConnection_zero (n : ℕ) (h : 0 ≤ n) (α : Bool) (x : cube.{u} (n + 2)) :
    cubeConnection n 0 h α x = (globeOneConnection α (x.1, x.2.1), x.2.2) :=
  rfl

@[simp] theorem cubeConnection_succ (n i : ℕ) (h : i + 1 ≤ n + 1) (α : Bool)
    (x : cube.{u} (n + 3)) :
    cubeConnection (n + 1) (i + 1) h α x =
      (x.1, cubeConnection n i (Nat.le_of_succ_le_succ h) α x.2) :=
  rfl

theorem isMap_cubeConnection (n i : ℕ) (h : i ≤ n) (α : Bool) :
    IsMap (cubeConnection.{u} n i h α) := by
  induction i generalizing n with
  | zero =>
    exact (isMap_of_isInclusion (grayProductAssoc (globe 1) (globe 1) (cube n)).inv).comp
      (isMap_prod_left_of_isMap isRDC_square isRDC_globe_one (isRDC_cube n)
        (isMap_globeOneConnection α))
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact isMap_prod_right_of_isMap isRDC_globe_one (isRDC_cube (n + 2)) (isRDC_cube (n + 1))
      (ih n (Nat.le_of_succ_le_succ h))

theorem surjective_cubeConnection (n i : ℕ) (h : i ≤ n) (α : Bool) :
    Function.Surjective (cubeConnection.{u} n i h α) := by
  induction i generalizing n with
  | zero =>
    rintro ⟨a, x⟩
    exact ⟨(a, (pole (!α), x)), congrArg (·, x) (globeOneConnection_pole_not_right α a)⟩
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rintro ⟨a, x⟩
    obtain ⟨y, rfl⟩ := ih n (Nat.le_of_succ_le_succ h) x
    exact ⟨(a, y), rfl⟩

theorem cubeConnection_cubeCoface_not (n i : ℕ) (h : i ≤ n) (α : Bool) (x : cube.{u} (n + 1)) :
    cubeConnection n i h α (cubeCoface (n + 1) i (Nat.le_succ_of_le h) (!α) x) = x := by
  induction i generalizing n with
  | zero => exact Prod.ext (globeOneConnection_pole_not_left α x.1) rfl
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Prod.ext rfl (ih n (Nat.le_of_succ_le_succ h) x.2)

theorem cubeConnection_cubeCoface_succ_not (n i : ℕ) (h : i ≤ n) (α : Bool)
    (x : cube.{u} (n + 1)) :
    cubeConnection n i h α (cubeCoface (n + 1) (i + 1) (Nat.succ_le_succ h) (!α) x) = x := by
  induction i generalizing n with
  | zero => exact Prod.ext (globeOneConnection_pole_not_right α x.1) rfl
  | succ i ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Prod.ext rfl (ih n (Nat.le_of_succ_le_succ h) x.2)

def cubeEquiv : (n : ℕ) → cube.{u} n ≃ (Fin n → globe.{u} 1)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => (⊤ : point.{u})
      left_inv := fun _ => Subsingleton.elim (α := PUnit) _ _
      right_inv := fun _ => funext fun i => Fin.elim0 i }
  | n + 1 => (Equiv.prodCongr (Equiv.refl (globe.{u} 1)) (cubeEquiv n)).trans
      (Fin.consEquiv fun _ => globe.{u} 1)

theorem cubeEquiv_succ (n : ℕ) (x : cube.{u} (n + 1)) :
    cubeEquiv (n + 1) x = Fin.cons x.1 (cubeEquiv n x.2) :=
  rfl

@[simp] theorem cubeEquiv_succ_apply_zero (n : ℕ) (x : cube.{u} (n + 1)) :
    cubeEquiv (n + 1) x 0 = x.1 :=
  rfl

@[simp] theorem cubeEquiv_succ_apply_succ (n : ℕ) (x : cube.{u} (n + 1)) (i : Fin n) :
    cubeEquiv (n + 1) x i.succ = cubeEquiv n x.2 i :=
  rfl

private theorem grade_globe_one (a : globe.{u} 1) : grade ℕ a = if a = ⊤ then 1 else 0 := by
  split_ifs with h
  · rw [h, grade_top_globe]
  · rcases a with β | ⟨⟨⟩⟩
    · rfl
    · exact (h rfl).elim

private theorem card_filter_cons_eq_top {n : ℕ} (a : globe.{u} 1) (c : Fin n → globe.{u} 1) :
    (Finset.univ.filter fun i => (Fin.cons a c : Fin (n + 1) → globe.{u} 1) i = ⊤).card =
      grade ℕ a + (Finset.univ.filter fun i => c i = ⊤).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, grade_globe_one]
  simp only [Fin.cons_zero, Fin.cons_succ]

private theorem card_filter_lt_succ {n : ℕ} (a : globe.{u} 1) (c : Fin n → globe.{u} 1)
    (i : Fin n) :
    (Finset.univ.filter fun k => k < i.succ ∧
        (Fin.cons a c : Fin (n + 1) → globe.{u} 1) k = ⊤).card =
      grade ℕ a + (Finset.univ.filter fun k => k < i ∧ c k = ⊤).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, grade_globe_one]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, true_and, Fin.succ_lt_succ_iff]

theorem grade_cube {n : ℕ} (x : cube.{u} n) :
    grade ℕ x = (Finset.univ.filter fun i => cubeEquiv n x i = ⊤).card := by
  induction n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty]
    exact (isMin_point (x : point.{u})).grade (𝕆 := ℕ) |>.eq_bot
  | succ n ih =>
    rw [cubeEquiv_succ, card_filter_cons_eq_top, ← ih x.2]
    exact Prod.grade_eq_add (α := globe.{u} 1) (β := cube.{u} n) x

private theorem mem_faces_globe_one {α : Bool} {a b : globe.{u} 1} :
    b ∈ (globe.{u} 1).faces α a ↔ a = ⊤ ∧ b = pole α := by
  rcases a with β | ⟨⟨⟩⟩
  · refine iff_of_false (fun h => not_covBy_pole h.1) ?_
    rintro ⟨h, -⟩
    cases h
  · refine ⟨fun h => ⟨rfl, ?_⟩, ?_⟩
    · rcases b with γ | ⟨⟨⟩⟩
      · exact congrArg pole ((pole_mem_faces_suspension (P := globe 0)).1 h).2
      · exact (h.1.lt.ne rfl).elim
    · rintro ⟨-, rfl⟩
      exact (pole_mem_faces_suspension (P := globe 0)).2 ⟨isMin_point _, rfl⟩

theorem mem_faces_cube_iff {n : ℕ} {x y : cube.{u} n} {α : Bool} :
    y ∈ (cube.{u} n).faces α x ↔ ∃ j, cubeEquiv n x j = ⊤ ∧
      cubeEquiv n y = Function.update (cubeEquiv n x) j
        (pole (xor α (Finset.univ.filter fun i => i < j ∧ cubeEquiv n x i = ⊤).card.bodd)) := by
  induction n generalizing α with
  | zero =>
    refine iff_of_false (fun h => (isMin_point (x : point.{u})).not_lt h.1.lt) ?_
    rintro ⟨j, -⟩
    exact j.elim0
  | succ n ih =>
    rw [cubeEquiv_succ n x, cubeEquiv_succ n y, Fin.exists_fin_succ]
    refine (mem_faces_grayProduct (P := globe.{u} 1) (Q := cube.{u} n)).trans ?_
    rw [ih, mem_faces_globe_one]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update, Fin.cons_inj,
      card_filter_lt_succ, Fin.not_lt_zero, false_and, Finset.filter_false, Finset.card_empty,
      Nat.bodd_zero, Bool.xor_false, Equiv.apply_eq_iff_eq, Nat.bodd_add]
    have hxor (g c : Bool) : xor (xor g α) c = xor α (xor g c) := by
      cases g <;> cases α <;> cases c <;> rfl
    simp only [hxor, and_assoc]
    refine or_congr Iff.rfl ⟨fun ⟨h₁, j, hj, hy⟩ => ⟨j, hj, h₁, hy⟩,
      fun ⟨j, hj, h₁, hy⟩ => ⟨h₁, j, hj, hy⟩⟩

private theorem univ_globe_one :
    (Finset.univ : Finset (globe.{u} 1)) = {pole false, pole true, ⊤} := by
  refine (Finset.eq_univ_iff_forall.2 fun a => ?_).symm
  rcases a with (_ | _) | ⟨⟨⟩⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

private theorem sum_X_pow_grade_cube (n : ℕ) :
    ∑ x : cube.{u} n, (Polynomial.X : Polynomial ℕ) ^ grade ℕ x =
      (Polynomial.X + Polynomial.C 2) ^ n := by
  induction n with
  | zero =>
    refine (Fintype.sum_equiv (ι := cube.{u} 0) (κ := PUnit.{u + 1}) (Equiv.refl _) _
      (fun _ => 1) fun x => (congrArg (fun m => (Polynomial.X : Polynomial ℕ) ^ m)
        ((isMin_point (x : point.{u})).grade (𝕆 := ℕ)).eq_bot).trans (pow_zero _)).trans ?_
    rw [pow_zero, Fintype.sum_unique]
  | succ n ih =>
    refine (Fintype.sum_equiv (ι := cube.{u} (n + 1)) (κ := globe.{u} 1 × cube.{u} n)
      (Equiv.refl _) _
      (fun p => (Polynomial.X : Polynomial ℕ) ^ grade ℕ p.1 * Polynomial.X ^ grade ℕ p.2)
      fun p => (congrArg (fun m => (Polynomial.X : Polynomial ℕ) ^ m)
        (Prod.grade_eq_add (α := globe.{u} 1) (β := cube.{u} n) p)).trans (pow_add _ _ _)).trans ?_
    rw [Fintype.sum_prod_type' (fun a y => (Polynomial.X : Polynomial ℕ) ^ grade ℕ a *
        Polynomial.X ^ grade ℕ y), ← Finset.sum_mul_sum, ih, pow_succ', univ_globe_one,
      Finset.sum_insert (by
        rw [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by rintro ⟨⟩, by rintro ⟨⟩⟩),
      Finset.sum_insert (by
        rw [Finset.mem_singleton]
        rintro ⟨⟩), Finset.sum_singleton,
      grade_pole, grade_pole, grade_top_globe, pow_zero, pow_one, map_ofNat]
    ring

theorem card_filter_grade_cube (n k : ℕ) :
    (Finset.univ.filter fun x : cube.{u} n => grade ℕ x = k).card = 2 ^ (n - k) * n.choose k := by
  have h := congrArg (Polynomial.coeff · k) (sum_X_pow_grade_cube.{u} n)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_X_add_C_pow,
    Nat.cast_id] at h
  rw [← h, Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => if_congr eq_comm rfl rfl

end Atoms.Molecule.OGP
