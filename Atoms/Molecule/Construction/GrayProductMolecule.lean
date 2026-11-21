import Atoms.Molecule.Construction.Suspension
import Atoms.Molecule.Construction.GrayProduct
import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.Pasting.AtSubmolecule
import Mathlib.Data.Set.Card

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

private structure ProductLevel (U : LowerSet P) (V : LowerSet Q) (n : ℕ) : Prop where
  mol : ∀ α, IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α)
  left : ∀ α j, (grayProduct P Q).IsSubmoleculeOf
    ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
    ((grayProduct P Q).boundary (U ×ˢ V) n α)
  right : ∀ α i, (grayProduct P Q).IsSubmoleculeOf
    ((grayProduct P Q).boundary (U ×ˢ Q.boundary V i (xor (n + i).bodd α)) n α)
    ((grayProduct P Q).boundary (U ×ˢ V) n α)
  splitLeft : ∀ k α A B, IsMoleculeIn P A → IsMoleculeIn P B → A < U → B < U →
    P.IsPastingIn k (cond α A B) (cond α B A) U → (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (B ×ˢ V) n α) ((grayProduct P Q).boundary (U ×ˢ V) n α)
  splitRight : ∀ k β A B, IsMoleculeIn Q A → IsMoleculeIn Q B → A < V → B < V →
    Q.IsPastingIn k (cond β A B) (cond β B A) V → (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (U ×ˢ B) n (xor (n + k).bodd β))
      ((grayProduct P Q).boundary (U ×ˢ V) n (xor (n + k).bodd β))

private def ProductStatement (U : LowerSet P) (V : LowerSet Q) : Prop :=
  IsMoleculeIn (grayProduct P Q) (U ×ˢ V) ∧ ∀ n, ProductLevel U V n

private theorem ProductLevel.term {U : LowerSet P} {V : LowerSet Q} {n k : ℕ} {α : Bool}
    (h : ProductLevel U V n) (h' : ProductLevel (P.boundary U k α) V n) (hk : k ≤ n) :
    (grayProduct P Q).IsSubmoleculeOf
      (P.boundary U k α ×ˢ Q.boundary V (n - k) (xor k.bodd α))
      ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have h1 := h'.right α (n - k)
  rw [Nat.bodd_add_of_eq_add (show n = n - k + k by omega),
    boundary_prod_boundary_eq_self U V (show k + (n - k) ≤ n by omega)] at h1
  exact h1.trans (h.left α k)

private theorem boundary_Iic_of_isMin {R : OGP.{u}} {z : R} (hz : IsMin z) (j : ℕ) (α : Bool) :
    R.boundary (LowerSet.Iic z) j α = LowerSet.Iic z := by
  exact boundary_eq_self
    ((LowerSet.krullDim_Iic_of_isMin hz).trans_le (by exact_mod_cast Nat.zero_le j)) α

private theorem not_isMoleculeIn_of_lt_Iic {R : OGP.{u}} {z : R} (hz : IsMin z)
    {W : LowerSet R} (hW : IsMoleculeIn R W) (hlt : W < LowerSet.Iic z) : False := by
  obtain ⟨y, hy⟩ := hW.nonempty
  have hyz : y = z := le_antisymm (hlt.le hy) (hz (hlt.le hy))
  exact hlt.not_ge fun w hw => W.lower hw (hyz ▸ hy)

private theorem productStatement_Iic_left {x : P} (hx : IsMin x)
    {V : LowerSet Q} (hV : IsMoleculeIn Q V) : ProductStatement (.Iic x) V := by
  refine ⟨(isMoleculeIn_Iic_prod_iff hx V).2 hV, fun n => ⟨fun α => ?_, fun α j => ?_,
    fun α i => ?_, fun k α A B _ hB _ hBU _ => ?_, fun k β A B hA hB _ _ hp => ?_⟩⟩
  · rw [boundary_Iic_prod hx]
    exact (isMoleculeIn_Iic_prod_iff hx _).2 (hV.boundary n α)
  · rw [boundary_Iic_of_isMin hx, boundary_Iic_prod hx]
    exact .refl ((isMoleculeIn_Iic_prod_iff hx _).2 (hV.boundary n α))
  · rw [boundary_Iic_prod hx, boundary_Iic_prod hx, isSubmoleculeOf_Iic_prod_iff hx]
    rcases lt_trichotomy i n with h | rfl | h
    · exact hV.boundary_boundary_isSubmoleculeOf_boundary (Or.inl h)
    · exact hV.boundary_boundary_isSubmoleculeOf_boundary (Or.inr (by simp [Nat.bodd_add]))
    · rw [hV.isGlobular n i h]
      exact .refl (hV.boundary n α)
  · exact (not_isMoleculeIn_of_lt_Iic hx hB hBU).elim
  · rw [boundary_Iic_prod hx, boundary_Iic_prod hx, isSubmoleculeOf_Iic_prod_iff hx]
    rcases lt_trichotomy k n with h | rfl | h
    · exact hp.boundary_isSubmoleculeOf_boundary β hA hB (Or.inl h)
    · exact hp.boundary_isSubmoleculeOf_boundary β hA hB (Or.inr (by simp [Nat.bodd_add]))
    · rw [hp.boundary_eq_of_lt_cond β hA.isGlobular hB.isGlobular h]
      exact .refl (hB.boundary n _)

private def ProductBelow (U : LowerSet P) (V : LowerSet Q) : Prop :=
  ∀ (U' : LowerSet P) (V' : LowerSet Q),
    (U' : Set P).ncard + (V' : Set Q).ncard < (U : Set P).ncard + (V : Set Q).ncard →
    IsMoleculeIn P U' → IsMoleculeIn Q V' → ProductStatement U' V'

private theorem ncard_add_ncard_lt_left {U' U : LowerSet P} {V' V : LowerSet Q}
    (fU : (U : Set P).Finite) (fV : (V : Set Q).Finite) (hU : U' < U) (hV : V' ≤ V) :
    (U' : Set P).ncard + (V' : Set Q).ncard < (U : Set P).ncard + (V : Set Q).ncard :=
  Nat.add_lt_add_of_lt_of_le (Set.ncard_lt_ncard hU fU) (Set.ncard_le_ncard hV fV)

private theorem ncard_add_ncard_lt_right {U' U : LowerSet P} {V' V : LowerSet Q}
    (fU : (U : Set P).Finite) (fV : (V : Set Q).Finite) (hU : U' ≤ U) (hV : V' < V) :
    (U' : Set P).ncard + (V' : Set Q).ncard < (U : Set P).ncard + (V : Set Q).ncard :=
  Nat.add_lt_add_of_le_of_lt (Set.ncard_le_ncard hU fU) (Set.ncard_lt_ncard hV fV)

private theorem map_boundary_prod_swap (X : LowerSet P) (Y : LowerSet Q) (n : ℕ) (α : Bool) :
    map (grayProductSwap P Q).inv
        ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (Y ×ˢ X) n α) =
      (grayProduct P Q).boundary (X ×ˢ Y) n (xor (n + 1).bodd α) := by
  rw [map_boundary, map_grayProductSwap_inv_prod, boundary_dual]

private theorem isMoleculeIn_prod_swap {X : LowerSet P} {Y : LowerSet Q} :
    IsMoleculeIn (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)) (Y ×ˢ X) ↔
      IsMoleculeIn (grayProduct P Q) (X ×ˢ Y) := by
  rw [← isMoleculeIn_map_iff (grayProductSwap P Q).inv, map_grayProductSwap_inv_prod,
    isMoleculeIn_dual]

private theorem isMoleculeIn_boundary_prod_swap {X : LowerSet P} {Y : LowerSet Q} {n : ℕ}
    {α : Bool} :
    IsMoleculeIn (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd))
        ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (Y ×ˢ X) n α) ↔
      IsMoleculeIn (grayProduct P Q)
        ((grayProduct P Q).boundary (X ×ˢ Y) n (xor (n + 1).bodd α)) := by
  rw [← isMoleculeIn_map_iff (grayProductSwap P Q).inv, map_boundary_prod_swap,
    isMoleculeIn_dual]

private theorem isSubmoleculeOf_boundary_prod_swap {X U : LowerSet P} {Y V : LowerSet Q}
    {n : ℕ} {α : Bool} :
    (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).IsSubmoleculeOf
        ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (Y ×ˢ X) n α)
        ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (V ×ˢ U) n α) ↔
      (grayProduct P Q).IsSubmoleculeOf
        ((grayProduct P Q).boundary (X ×ˢ Y) n (xor (n + 1).bodd α))
        ((grayProduct P Q).boundary (U ×ˢ V) n (xor (n + 1).bodd α)) := by
  rw [← isSubmoleculeOf_map_iff (grayProductSwap P Q).inv, map_boundary_prod_swap,
    map_boundary_prod_swap, isSubmoleculeOf_dual]

private theorem right_swap_of_left {U : LowerSet P} {V : LowerSet Q} {n : ℕ}
    (h : ∀ α j, (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α)) (α : Bool) (i : ℕ) :
    (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).IsSubmoleculeOf
      ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary
        (V ×ˢ (dual P Nat.bodd).boundary U i (xor (n + i).bodd α)) n α)
      ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (V ×ˢ U) n α) :=
  isSubmoleculeOf_boundary_prod_swap.2 (by
    rw [boundary_dual, show xor (i + 1).bodd (xor (n + i).bodd α) = xor (n + 1).bodd α by
      simp [Nat.bodd_add, Bool.xor_left_comm, Bool.xor_comm]]
    exact h _ i)

private theorem splitRight_swap_of_splitLeft {U : LowerSet P} {V : LowerSet Q} {n : ℕ}
    (h : ∀ k α A B, IsMoleculeIn P A → IsMoleculeIn P B → A < U → B < U →
      P.IsPastingIn k (cond α A B) (cond α B A) U → (grayProduct P Q).IsSubmoleculeOf
        ((grayProduct P Q).boundary (B ×ˢ V) n α) ((grayProduct P Q).boundary (U ×ˢ V) n α))
    (k : ℕ) (β : Bool) (A B : LowerSet (dual P Nat.bodd))
    (mA : IsMoleculeIn (dual P Nat.bodd) A) (mB : IsMoleculeIn (dual P Nat.bodd) B) (sA : A < U)
    (sB : B < U) (hp : (dual P Nat.bodd).IsPastingIn k (cond β A B) (cond β B A) U) :
    (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).IsSubmoleculeOf
      ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (V ×ˢ B) n
        (xor (n + k).bodd β))
      ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary (V ×ˢ U) n
        (xor (n + k).bodd β)) :=
  isSubmoleculeOf_boundary_prod_swap.2 (by
    rw [show xor (n + 1).bodd (xor (n + k).bodd β) = xor (k + 1).bodd β by
      simp [Nat.bodd_add, Bool.xor_left_comm, Bool.xor_comm]]
    exact h k _ A B ((isMoleculeIn_dual _).1 mA) ((isMoleculeIn_dual _).1 mB) sA sB
      ((isPastingIn_cond_dual _ β).1 hp))

private theorem ProductLevel.swap {U : LowerSet P} {V : LowerSet Q} {n : ℕ}
    (h : ProductLevel U V n) :
    ProductLevel (P := dual Q Nat.bodd) (Q := dual P Nat.bodd) V U n where
  mol _ := isMoleculeIn_boundary_prod_swap.2 (h.mol _)
  left α j := isSubmoleculeOf_boundary_prod_swap.2 (by
    rw [boundary_dual, ← show xor (n + j).bodd (xor (n + 1).bodd α) = xor (j + 1).bodd α by
      simp [Nat.bodd_add, Bool.xor_left_comm, Bool.xor_comm]]
    exact h.right _ j)
  right := right_swap_of_left h.left
  splitLeft k γ A B mA mB sA sB hp := isSubmoleculeOf_boundary_prod_swap.2 (by
    rw [← show xor (n + k).bodd (xor (k + 1).bodd γ) = xor (n + 1).bodd γ by
      simp [Nat.bodd_add, Bool.xor_left_comm, Bool.xor_comm]]
    exact h.splitRight k _ A B ((isMoleculeIn_dual _).1 mA) ((isMoleculeIn_dual _).1 mB) sA sB
      ((isPastingIn_cond_dual _ γ).1 hp))
  splitRight := splitRight_swap_of_splitLeft h.splitLeft

private theorem of_dual_dual {Φ : ∀ P Q : OGP.{u}, LowerSet P → LowerSet Q → Prop}
    {U : LowerSet P} {V : LowerSet Q}
    (h : Φ (dual (dual P Nat.bodd) Nat.bodd) (dual (dual Q Nat.bodd) Nat.bodd) U V) :
    Φ P Q U V :=
  (congrArg₂ (fun o₁ o₂ => Φ { P with orient := o₁ } { Q with orient := o₂ } U V)
    (orient_dual_dual P Nat.bodd) (orient_dual_dual Q Nat.bodd)).mp h

private theorem productLevel_swap_iff {U : LowerSet P} {V : LowerSet Q} {n : ℕ} :
    ProductLevel (P := dual Q Nat.bodd) (Q := dual P Nat.bodd) V U n ↔ ProductLevel U V n :=
  ⟨fun h => of_dual_dual (Φ := fun _ _ U V => ProductLevel U V n) h.swap, ProductLevel.swap⟩

private theorem productStatement_swap_iff {U : LowerSet P} {V : LowerSet Q} :
    ProductStatement (P := dual Q Nat.bodd) (Q := dual P Nat.bodd) V U ↔ ProductStatement U V :=
  and_congr isMoleculeIn_prod_swap (forall_congr' fun _ => productLevel_swap_iff)

private theorem ProductBelow.swap {U : LowerSet P} {V : LowerSet Q} (IH : ProductBelow U V) :
    ProductBelow (P := dual Q Nat.bodd) (Q := dual P Nat.bodd) V U :=
  fun V' U' hlt hV' hU' => productStatement_swap_iff.2 (IH U' V'
    ((Nat.add_comm _ _).trans_lt (hlt.trans_eq (Nat.add_comm _ _)))
    ((isMoleculeIn_dual _).1 hU') ((isMoleculeIn_dual _).1 hV'))

private theorem isMoleculeIn_boundary_prod_of_split {U X₁ X₂ : LowerSet P}
    {V Y₁ Y₂ : LowerSet Q} {Z : LowerSet (grayProduct P Q)}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V)
    (hX₁ : P.IsSubmoleculeOf X₁ U) (hY₁ : Q.IsSubmoleculeOf Y₁ V)
    (hX₂ : P.IsSubmoleculeOf X₂ U) (hY₂ : Q.IsSubmoleculeOf Y₂ V)
    (m₁ : IsMoleculeIn (grayProduct P Q) (X₁ ×ˢ Y₁))
    (m₂ : IsMoleculeIn (grayProduct P Q) (X₂ ×ˢ Y₂)) {n : ℕ} (hn1 : n - 1 < n) (α : Bool)
    (hE : (grayProduct P Q).boundary (X₁ ×ˢ Y₁) n α ⊔ (grayProduct P Q).boundary (X₂ ×ˢ Y₂) n α =
      (grayProduct P Q).boundary (U ×ˢ V) n α)
    (hI : (grayProduct P Q).boundary (X₁ ×ˢ Y₁) n α ⊓ (grayProduct P Q).boundary (X₂ ×ˢ Y₂) n α =
      Z)
    (h1 : (grayProduct P Q).IsSubmoleculeOf Z
      ((grayProduct P Q).boundary (X₁ ×ˢ Y₁) (n - 1) (!α)))
    (h2 : (grayProduct P Q).IsSubmoleculeOf Z
      ((grayProduct P Q).boundary (X₂ ×ˢ Y₂) (n - 1) α))
    (h3 : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (X₁ ×ˢ Y₁) (n - 1) α)
      ((grayProduct P Q).boundary (U ×ˢ V) (n - 1) α))
    (h4 : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (X₂ ×ˢ Y₂) (n - 1) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (n - 1) (!α))) :
    IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (X₁ ×ˢ Y₁) n α)
        ((grayProduct P Q).boundary (U ×ˢ V) n α) ∧
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (X₂ ×ˢ Y₂) n α)
        ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have gX₁ := hX₁.isMoleculeIn.isGlobular
  have gX₂ := hX₂.isMoleculeIn.isGlobular
  have gY₁ := hY₁.isMoleculeIn.isGlobular
  have gY₂ := hY₂.isMoleculeIn.isGlobular
  have hZ (γ : Bool) :
      (grayProduct P Q).boundary ((grayProduct P Q).boundary (U ×ˢ V) n α) (n - 1) γ =
      (grayProduct P Q).boundary (U ×ˢ V) (n - 1) γ :=
    isGlobular_prod hU.isGlobular hV.isGlobular (n - 1) n hn1 γ α
  have hA (γ : Bool) :
      (grayProduct P Q).boundary ((grayProduct P Q).boundary (X₁ ×ˢ Y₁) n α) (n - 1) γ =
      (grayProduct P Q).boundary (X₁ ×ˢ Y₁) (n - 1) γ :=
    isGlobular_prod gX₁ gY₁ (n - 1) n hn1 γ α
  have hB (γ : Bool) :
      (grayProduct P Q).boundary ((grayProduct P Q).boundary (X₂ ×ˢ Y₂) n α) (n - 1) γ =
      (grayProduct P Q).boundary (X₂ ×ˢ Y₂) (n - 1) γ :=
    isGlobular_prod gX₂ gY₂ (n - 1) n hn1 γ α
  have h5 := inf_boundary_boundary_prod_le hU hV hX₁ hY₁ hn1 α α
  have h6 := inf_boundary_boundary_prod_le hU hV hX₂ hY₂ hn1 α (!α)
  rw [← hZ] at h5 h6
  exact isMoleculeIn_and_isSubmoleculeOf_of_genPasting α hE.symm (m₁.boundary n α)
    (m₂.boundary n α) (by rw [hI, hA]; exact h1) (by rw [hI, hB]; exact h2)
    (by rw [hA, hZ]; exact h3) (by rw [hB, hZ]; exact h4) h5 h6

private theorem boundary_prod_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {d m n j : ℕ}
    (hdU : krullDim U = d) (hmV : krullDim V = m)
    (hjn : j < n) (hjU : j < d) (hjV : n - m ≤ j)
    (hprev : ProductLevel U V (n - 1)) (α : Bool) :
    IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α) ∧
      (grayProduct P Q).IsSubmoleculeOf
        ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
        ((grayProduct P Q).boundary (U ×ˢ V) n α) ∧
      (grayProduct P Q).IsSubmoleculeOf
        ((grayProduct P Q).boundary (U ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) n α)
        ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have fU := hU.finite
  have fV := hV.finite
  have gU := hU.isGlobular
  have gV := hV.isGlobular
  have hn1 : n - 1 < n := by omega
  set X := P.boundary U j α
  set Y := Q.boundary V (n - j - 1) (xor (j + 1).bodd α)
  have mX : IsMoleculeIn P X := hU.boundary j α
  have mY : IsMoleculeIn Q Y := hV.boundary _ _
  have sXU : X < U := boundary_lt_iff.2 (by rw [hdU]; exact_mod_cast hjU)
  have sYV : Y < V :=
    boundary_lt_iff.2 (by rw [hmV]; exact_mod_cast (show n - j - 1 < m by omega))
  have SX := IH X V (ncard_add_ncard_lt_left fU fV sXU le_rfl) mX hV
  have SY := IH U Y (ncard_add_ncard_lt_right fU fV le_rfl sYV) hU mY
  have SXY := IH X Y (ncard_add_ncard_lt_left fU fV sXU sYV.le) mX mY
  have SXX := IH (P.boundary X j (!α)) V
    (ncard_add_ncard_lt_left fU fV ((boundary_le X j _).trans_lt sXU) le_rfl)
    (mX.boundary j _) hV
  have hs : xor j.bodd (!α) = xor (j + 1).bodd α := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.xor_not]
  have hI : (grayProduct P Q).boundary (X ×ˢ V) n α ⊓ (grayProduct P Q).boundary (U ×ˢ Y) n α =
      X ×ˢ Y := boundary_prod_inf gU gV hjn α
  have h1 : (grayProduct P Q).IsSubmoleculeOf (X ×ˢ Y)
      ((grayProduct P Q).boundary (X ×ˢ V) (n - 1) (!α)) := by
    have t := (SX.2 (n - 1)).term (SXX.2 (n - 1)) (show j ≤ n - 1 by omega)
    rw [boundary_eq_self (krullDim_boundary_le U j α), hs, show n - 1 - j = n - j - 1 by omega] at t
    exact t
  have h2 : (grayProduct P Q).IsSubmoleculeOf (X ×ˢ Y)
      ((grayProduct P Q).boundary (U ×ˢ Y) (n - 1) α) := by
    have t := (SY.2 (n - 1)).term (SXY.2 (n - 1)) (show j ≤ n - 1 by omega)
    rwa [boundary_eq_self
      ((krullDim_boundary_le V _ _).trans (by exact_mod_cast (by omega)))] at t
  have h4 : (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (U ×ˢ Y) (n - 1) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (n - 1) (!α)) := by
    have t := hprev.right (!α) (n - j - 1)
    rwa [Nat.bodd_add_of_eq_add (show n - 1 = n - j - 1 + j by omega), hs] at t
  have hE : (grayProduct P Q).boundary (X ×ˢ V) n α ⊔ (grayProduct P Q).boundary (U ×ˢ Y) n α =
      (grayProduct P Q).boundary (U ×ˢ V) n α :=
    (boundary_prod_eq_sup gU gV hjn α).symm
  exact isMoleculeIn_boundary_prod_of_split hU hV (hU.boundary_isSubmoleculeOf j α)
    (.refl hV) (.refl hU) (hV.boundary_isSubmoleculeOf (n - j - 1) _) SX.1 SY.1 hn1 α hE hI h1 h2
    (hprev.left α j) h4

private theorem boundary_prod_splitLeft_pieces {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {k : ℕ} (α : Bool)
    {A B : LowerSet P} (mA : IsMoleculeIn P A) (mB : IsMoleculeIn P B) (sA : A < U) (sB : B < U)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {n : ℕ} (hkn : k < n) :
    IsMoleculeIn (grayProduct P Q) (B ×ˢ V) ∧
      IsMoleculeIn (grayProduct P Q) (A ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) ∧
      (grayProduct P Q).IsSubmoleculeOf
        (P.boundary B k (!α) ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α)))
        ((grayProduct P Q).boundary (B ×ˢ V) (n - 1) (!α)) ∧
      (grayProduct P Q).IsSubmoleculeOf
        (P.boundary B k (!α) ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α)))
        ((grayProduct P Q).boundary
          (A ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) (n - 1) α) := by
  have fU := hU.finite
  have fV := hV.finite
  obtain ⟨-, hAB0, hBA0⟩ := (isPastingIn_cond_iff α).1 hp
  set Y := Q.boundary V (n - k - 1) (xor k.bodd (!α))
  have mY : IsMoleculeIn Q Y := hV.boundary _ _
  have hYV : Y ≤ V := boundary_le V _ _
  have SB := IH B V (ncard_add_ncard_lt_left fU fV sB le_rfl) mB hV
  have SBk := IH (P.boundary B k (!α)) V
    (ncard_add_ncard_lt_left fU fV ((boundary_le B k _).trans_lt sB) le_rfl)
    (mB.boundary k _) hV
  have SA := IH A Y (ncard_add_ncard_lt_left fU fV sA hYV) mA mY
  have SAk := IH (P.boundary A k α) Y
    (ncard_add_ncard_lt_left fU fV ((boundary_le A k _).trans_lt sA) hYV)
    (mA.boundary k _) mY
  refine ⟨SB.1, SA.1, ?_, ?_⟩
  · have t := (SB.2 (n - 1)).term (SBk.2 (n - 1)) (show k ≤ n - 1 by omega)
    rwa [show n - 1 - k = n - k - 1 by omega] at t
  · have t := (SA.2 (n - 1)).term (SAk.2 (n - 1)) (show k ≤ n - 1 by omega)
    rwa [boundary_eq_self ((krullDim_boundary_le V _ _).trans (by exact_mod_cast (by omega))),
      ← hBA0, hAB0] at t

private theorem boundary_prod_splitLeft_not_isSubmoleculeOf {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {k : ℕ} (α : Bool)
    {A B : LowerSet P} (mA : IsMoleculeIn P A) (mB : IsMoleculeIn P B) (sA : A < U) (sB : B < U)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {n : ℕ} (hkn : k < n)
    (hprev : ProductLevel U V (n - 1)) :
    (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary
        (A ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) (n - 1) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (n - 1) (!α)) := by
  have fU := hU.finite
  have fV := hV.finite
  have hq := (isPastingIn_cond_comm α).1 hp
  set Y := Q.boundary V (n - k - 1) (xor k.bodd (!α))
  have mY : IsMoleculeIn Q Y := hV.boundary _ _
  by_cases hYlt : ((n - k - 1 : ℕ) : WithBot ℕ∞) < krullDim V
  · have sY : Y < V := boundary_lt_iff.2 hYlt
    have SUY := IH U Y (ncard_add_ncard_lt_right fU fV le_rfl sY) hU mY
    have t1 := (SUY.2 (n - 1)).splitLeft k (!α) B A mB mA sB sA hq
    have t2 := hprev.right (!α) (n - k - 1)
    rw [Nat.bodd_add_of_eq_add (show n - 1 = n - k - 1 + k by omega)] at t2
    exact t1.trans t2
  · have hYeq : Y = V := boundary_eq_self (not_lt.1 hYlt) _
    rw [hYeq]
    exact hprev.splitLeft k (!α) B A mB mA sB sA hq

private theorem boundary_prod_splitLeft_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {k : ℕ} (α : Bool)
    {A B : LowerSet P} (mA : IsMoleculeIn P A) (mB : IsMoleculeIn P B) (sA : A < U) (sB : B < U)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {n : ℕ} (hkn : k < n)
    (hprev : ProductLevel U V (n - 1)) :
    IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α) ∧
      (grayProduct P Q).IsSubmoleculeOf
        ((grayProduct P Q).boundary (B ×ˢ V) n α)
        ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have gA := mA.isGlobular
  have gB := mB.isGlobular
  have hq := (isPastingIn_cond_comm α).1 hp
  obtain ⟨-, hAB0, hBA0⟩ := (isPastingIn_cond_iff α).1 hp
  obtain ⟨mBV, mAY, h1, h2⟩ := boundary_prod_splitLeft_pieces hU hV IH α mA mB sA sB hp hkn
  have h4 := boundary_prod_splitLeft_not_isSubmoleculeOf hU hV IH α mA mB sA sB hp hkn hprev
  set Y := Q.boundary V (n - k - 1) (xor k.bodd (!α))
  have hE : (grayProduct P Q).boundary (B ×ˢ V) n α ⊔ (grayProduct P Q).boundary (A ×ˢ Y) n α =
      (grayProduct P Q).boundary (U ×ˢ V) n α :=
    (boundary_prod_eq_sup_of_split_left hU.isGlobular gB gA hV.isGlobular hkn
      (fun i hi => hp.boundary_eq_of_le_cond α gA gB hi)
      (fun i hi => hq.boundary_eq_sup_of_lt_cond (!α) gB gA hi α) (by rw [← hBA0, hAB0])
      (fun i hi => (hq.boundary_eq_of_lt_cond (!α) gB gA hi α).symm)).symm
  have hI : (grayProduct P Q).boundary (B ×ˢ V) n α ⊓ (grayProduct P Q).boundary (A ×ˢ Y) n α =
      P.boundary B k (!α) ×ˢ Y :=
    boundary_prod_inf_of_split_left gB gA hV.isGlobular hkn ((inf_comm B A).trans hAB0)
      ((inf_comm B A).trans hBA0)
  have key := isMoleculeIn_boundary_prod_of_split hU hV
    (hp.isPastingFactorOf α mB mA).isSubmoleculeOf (.refl hV)
    (hq.isPastingFactorOf (!α) mA mB).isSubmoleculeOf (hV.boundary_isSubmoleculeOf _ _) mBV mAY
    (by omega) α hE hI h1 h2 (hprev.splitLeft k α A B mA mB sA sB hp) h4
  exact ⟨key.1, key.2.1⟩

theorem boundary_prod_zero {U : LowerSet P} {V : LowerSet Q}
    (gU : P.IsGlobular U) (gV : Q.IsGlobular V) (α : Bool) :
    (grayProduct P Q).boundary (U ×ˢ V) 0 α = P.boundary U 0 α ×ˢ Q.boundary V 0 α := by
  refine le_antisymm ?_ ?_
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular gU gV).1 h
    obtain rfl : i = 0 := by omega
    exact ⟨ha, by simpa using hb⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact (mem_boundary_prod_of_isGlobular gU gV).2 ⟨0, le_rfl, ha, by simpa using hb⟩

theorem isMoleculeIn_boundary_prod_zero {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (α : Bool) :
    IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) 0 α) := by
  rw [boundary_prod_zero hU.isGlobular hV.isGlobular]
  obtain ⟨d, hd⟩ := (hU.boundary 0 α).exists_krullDim_eq
  obtain ⟨x, hx, hUx⟩ := (hU.boundary 0 α).exists_eq_Iic_of_krullDim_eq_zero
    (le_antisymm (krullDim_boundary_le U 0 α) (hd ▸ by exact_mod_cast Nat.zero_le d))
  rw [hUx]
  exact (isMoleculeIn_Iic_prod_iff hx _).2 (hV.boundary 0 α)

section Trivial

variable {U : LowerSet P} {V : LowerSet Q}

theorem boundary_prod_boundary_left_of_le (gU : P.IsGlobular U) (gV : Q.IsGlobular V)
    {n j : ℕ} (hnj : n ≤ j) (α : Bool) :
    (grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α =
      (grayProduct P Q).boundary (U ×ˢ V) n α :=
  boundary_prod_congr (gU.boundary j α) gU gV gV
    (fun _ hi => gU.boundary_boundary_eq_of_le (hi.trans hnj) (Or.inr rfl))
    (fun _ _ => rfl)

theorem boundary_prod_cond_left_of_le (α : Bool) {k : ℕ} {A B : LowerSet P}
    (gA : P.IsGlobular A) (gB : P.IsGlobular B) (gV : Q.IsGlobular V)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) {n : ℕ} (hnk : n ≤ k) :
    (grayProduct P Q).boundary (B ×ˢ V) n α = (grayProduct P Q).boundary (U ×ˢ V) n α :=
  boundary_prod_congr gB (hp.isGlobular (Bool.cond_rec_prop α gA gB) (Bool.cond_rec_prop α gB gA))
    gV gV (fun _ hi => (hp.boundary_eq_of_le_cond α gA gB (hi.trans hnk)).symm) fun _ _ => rfl

end Trivial

theorem Iic_grayProduct (p : P) (q : Q) :
    LowerSet.Iic ((p, q) : grayProduct P Q) = LowerSet.Iic p ×ˢ LowerSet.Iic q :=
  SetLike.ext fun ⟨_, _⟩ => Iff.rfl

private theorem isMoleculeIn_prod_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {d m : ℕ}
    (hdU : krullDim U = d) (hmV : krullDim V = m) (hd : 0 < d) (hm : 0 < m)
    (hprev : ProductLevel U V (d + m - 1)) :
    IsMoleculeIn (grayProduct P Q) (U ×ˢ V) := by
  have hN : (grayProduct P Q).boundary (U ×ˢ V) (d + m) false = U ×ˢ V :=
    boundary_prod_eq_self hdU.le hmV.le le_rfl false
  have hU0 := hU
  cases hU0 with
  | point x hx =>
    rw [LowerSet.krullDim_Iic_of_isMin hx] at hdU
    exact absurd (by exact_mod_cast hdU.symm : d = 0) hd.ne'
  | paste k W W' _ hp hW hW' hk =>
    have sW : W < U := hp.lt_cond false (hk.trans_le (min_le_right _ _))
    have sW' : W' < U := hp.lt_cond true (hk.trans_le (min_le_left _ _))
    have hkd : k < d := by
      exact_mod_cast (hk.trans_le (min_le_left _ _)).trans_le
        ((LowerSet.krullDim_mono hp.left_le).trans_eq hdU)
    have t := (boundary_prod_splitLeft_step hU hV IH false hW' hW sW' sW hp
      (n := d + m) (by omega) hprev).1
    rwa [hN] at t
  | atom tU hrU _ =>
    have hV0 := hV
    cases hV0 with
    | point y hy =>
      rw [LowerSet.krullDim_Iic_of_isMin hy] at hmV
      exact absurd (by exact_mod_cast hmV.symm : m = 0) hm.ne'
    | paste k W W' _ hp hW hW' hk =>
      have sW : W < V := hp.lt_cond false (hk.trans_le (min_le_right _ _))
      have sW' : W' < V := hp.lt_cond true (hk.trans_le (min_le_left _ _))
      have hkm : k < m := by
        exact_mod_cast (hk.trans_le (min_le_left _ _)).trans_le
          ((LowerSet.krullDim_mono hp.left_le).trans_eq hmV)
      have t := (boundary_prod_splitLeft_step ((isMoleculeIn_dual _).2 hV)
        ((isMoleculeIn_dual _).2 hU) IH.swap (k + 1).bodd ((isMoleculeIn_dual _).2 hW')
        ((isMoleculeIn_dual _).2 hW) sW' sW
        ((isPastingIn_cond_dual _ _).2 (by rwa [Bool.xor_self])) (n := d + m) (by omega)
        (productLevel_swap_iff.2 hprev)).1
      rwa [isMoleculeIn_boundary_prod_swap, boundary_prod_eq_self hdU.le hmV.le le_rfl] at t
    | atom tV hrV _ =>
      rw [← Iic_grayProduct]
      refine .atom (P := grayProduct P Q) (tU, tV)
        (Iic_grayProduct tU tV ▸ isRound_prod hrU hrV) fun α => ?_
      have hdim : krullDim (LowerSet.Iic ((tU, tV) : grayProduct P Q)) =
          ((d + m - 1 + 1 : ℕ) : WithBot ℕ∞) := by
        rw [Iic_grayProduct, krullDim_prod hdU hmV, show d + m - 1 + 1 = d + m by omega]
      rw [bdry_eq_boundary hdim, Iic_grayProduct]
      exact hprev.mol α

private theorem productLevel_mol_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {d m : ℕ}
    (hdU : krullDim U = d) (hmV : krullDim V = m) (hd : 0 < d) (hm : 0 < m) {n : ℕ}
    (hprev : ∀ i < n, ProductLevel U V i) (α : Bool) :
    IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  by_cases hnN : n < d + m
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact isMoleculeIn_boundary_prod_zero hU hV α
    · exact (boundary_prod_step hU hV IH hdU hmV (j := n - m) (by omega) (by omega) le_rfl
        (hprev _ (by omega)) α).1
  · rw [boundary_prod_eq_self hdU.le hmV.le (by omega) α]
    exact isMoleculeIn_prod_step hU hV IH hdU hmV hd hm (hprev _ (by omega))

private theorem productLevel_left_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {d m : ℕ}
    (hdU : krullDim U = d) (hmV : krullDim V = m) (hd : 0 < d) (hm : 0 < m) {n : ℕ}
    (hprev : ∀ i < n, ProductLevel U V i)
    (mol : ∀ α, IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α))
    (α : Bool) (j : ℕ) :
    (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have fU := hU.finite
  have fV := hV.finite
  have gU := hU.isGlobular
  have gV := hV.isGlobular
  have step : ∀ {j : ℕ}, j < n → j < d → n - m ≤ j → ∀ α, _ :=
    fun {j} hjn hjU hjV α => boundary_prod_step hU hV IH hdU hmV hjn hjU hjV (hprev _ (by omega)) α
  by_cases hjn : n ≤ j
  · rw [boundary_prod_boundary_left_of_le gU gV hjn]
    exact .refl (mol α)
  by_cases hjd : d ≤ j
  · rw [boundary_eq_self (hdU.le.trans (by exact_mod_cast hjd))]
    exact .refl (mol α)
  by_cases hnN : n < d + m
  · by_cases hjm : n - m ≤ j
    · exact (step (by omega) (by omega) hjm α).2.1
    · have sX : P.boundary U (n - m) α < U :=
        boundary_lt_iff.2 (by rw [hdU]; exact_mod_cast (show n - m < d by omega))
      have SX := IH _ V (ncard_add_ncard_lt_left fU fV sX le_rfl)
        (hU.boundary _ α) hV
      have t := (SX.2 n).left α j
      rw [gU j (n - m) (by omega) α α] at t
      exact t.trans (step (by omega) (by omega) le_rfl α).2.1
  · have t := (hprev (d + m - 1) (by omega)).left α j
    rw [boundary_prod_eq_self (krullDim_boundary_le U j α) hmV.le (by omega)] at t ⊢
    rw [boundary_prod_eq_self hdU.le hmV.le (by omega) α]
    exact t.trans ((isMoleculeIn_prod_step hU hV IH hdU hmV hd hm
      (hprev _ (by omega))).boundary_isSubmoleculeOf _ α)

private theorem productLevel_splitLeft_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {n : ℕ}
    (hprev : ∀ i < n, ProductLevel U V i)
    (mol : ∀ α, IsMoleculeIn (grayProduct P Q) ((grayProduct P Q).boundary (U ×ˢ V) n α))
    (k : ℕ) (α : Bool) (A B : LowerSet P) (mA : IsMoleculeIn P A) (mB : IsMoleculeIn P B)
    (sA : A < U) (sB : B < U) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) :
    (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (B ×ˢ V) n α) ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  by_cases hkn : k < n
  · exact (boundary_prod_splitLeft_step hU hV IH α mA mB sA sB hp hkn (hprev _ (by omega))).2
  · rw [boundary_prod_cond_left_of_le α mA.isGlobular mB.isGlobular hV.isGlobular hp
      (not_lt.1 hkn)]
    exact .refl (mol α)

private theorem productLevel_step {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (IH : ProductBelow U V) {d m : ℕ}
    (hdU : krullDim U = d) (hmV : krullDim V = m) (hd : 0 < d) (hm : 0 < m) {n : ℕ}
    (hprev : ∀ i < n, ProductLevel U V i) : ProductLevel U V n := by
  have mol := productLevel_mol_step hU hV IH hdU hmV hd hm hprev
  have hV' := (isMoleculeIn_dual Nat.bodd).2 hV
  have hU' := (isMoleculeIn_dual Nat.bodd).2 hU
  have hprev' (i : ℕ) (hi : i < n) := productLevel_swap_iff.2 (hprev i hi)
  have mol' (α : Bool) := isMoleculeIn_boundary_prod_swap.2 (mol (xor (n + 1).bodd α))
  exact productLevel_swap_iff.1 ⟨mol', productLevel_left_step hV' hU' IH.swap hmV hdU hm hd
    hprev' mol', right_swap_of_left (productLevel_left_step hU hV IH hdU hmV hd hm hprev mol),
    productLevel_splitLeft_step hV' hU' IH.swap hprev' mol',
    splitRight_swap_of_splitLeft (productLevel_splitLeft_step hU hV IH hprev mol)⟩

private theorem productStatement_of_isMoleculeIn {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) : ProductStatement U V := by
  induction hs : (U : Set P).ncard + (V : Set Q).ncard using Nat.strong_induction_on
      generalizing U V with
  | _ s ih =>
    have IH : ProductBelow U V := fun U' V' hlt hU' hV' => ih _ (hs ▸ hlt) hU' hV' rfl
    obtain ⟨d, hdU⟩ := hU.exists_krullDim_eq
    obtain ⟨m, hmV⟩ := hV.exists_krullDim_eq
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · obtain ⟨x, hx, rfl⟩ := hU.exists_eq_Iic_of_krullDim_eq_zero hdU
      exact productStatement_Iic_left hx hV
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨y, hy, rfl⟩ := hV.exists_eq_Iic_of_krullDim_eq_zero hmV
      exact productStatement_swap_iff.1 (productStatement_Iic_left (P := dual Q Nat.bodd)
        (Q := dual P Nat.bodd) hy ((isMoleculeIn_dual _).2 hU))
    have hlev : ∀ n, ProductLevel U V n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n hprev => exact productLevel_step hU hV IH hdU hmV hd hm hprev
    exact ⟨isMoleculeIn_prod_step hU hV IH hdU hmV hd hm (hlev _), hlev⟩

theorem isMoleculeIn_prod {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) :
    IsMoleculeIn (grayProduct P Q) (U ×ˢ V) :=
  (productStatement_of_isMoleculeIn hU hV).1

theorem isSubmoleculeOf_boundary_prod_boundary_left {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (n j : ℕ)
    (α : Bool) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α) :=
  ((productStatement_of_isMoleculeIn hU hV).2 n).left α j

theorem isSubmoleculeOf_boundary_prod_cond_left (α : Bool) {k : ℕ} {A B U : LowerSet P}
    {V : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B) (hAU : A < U) (hBU : B < U)
    (hV : IsMoleculeIn Q V) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (n : ℕ) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (B ×ˢ V) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α) :=
  ((productStatement_of_isMoleculeIn (hp.isMoleculeIn (Bool.cond_rec_prop α hA hB)
    (Bool.cond_rec_prop α hB hA)) hV).2 n).splitLeft k α A B hA hB hAU hBU hp

theorem isSubmoleculeOf_prod_boundary_boundary {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) {n k : ℕ}
    (hk : k ≤ n) (α : Bool) :
    (grayProduct P Q).IsSubmoleculeOf
      (P.boundary U k α ×ˢ Q.boundary V (n - k) (xor k.bodd α))
      ((grayProduct P Q).boundary (U ×ˢ V) n α) :=
  ProductLevel.term ((productStatement_of_isMoleculeIn hU hV).2 n)
    ((productStatement_of_isMoleculeIn (hU.boundary k α) hV).2 n) hk

theorem isSubmoleculeOf_boundary_prod_boundary_right {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (n i : ℕ) (α : Bool) :
    (grayProduct P Q).IsSubmoleculeOf
      ((grayProduct P Q).boundary (U ×ˢ Q.boundary V i (xor (n + i).bodd α)) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α) :=
  ((productStatement_of_isMoleculeIn hU hV).2 n).right α i

theorem isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn (α : Bool) {k : ℕ}
    {A B U : LowerSet P} {V : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B)
    (hV : IsMoleculeIn Q V) (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (n : ℕ) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (B ×ˢ V) n α)
      ((grayProduct P Q).boundary (U ×ˢ V) n α) := by
  have hU := hp.isMoleculeIn (Bool.cond_rec_prop α hA hB) (Bool.cond_rec_prop α hB hA)
  rcases hp.lt_or_eq_boundary α with ⟨hAU, hBU⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact isSubmoleculeOf_boundary_prod_cond_left α hA hB hAU hBU hV hp n
  · exact .refl ((isMoleculeIn_prod hU hV).boundary n α)
  · exact isSubmoleculeOf_boundary_prod_boundary_left hU hV n k α

private theorem isSubmoleculeOf_boundary_prod_cond_not_left (α : Bool) {k d n : ℕ}
    {A B U : LowerSet P} {X : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B)
    (hX : IsMoleculeIn Q X) (hdX : krullDim X ≤ d)
    (hp : P.IsPastingIn k (cond α A B) (cond α B A) U) (hn : k + d < n) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (A ×ˢ X) n α)
      ((grayProduct P Q).boundary (U ×ˢ X) n α) := by
  have hU := hp.isMoleculeIn (Bool.cond_rec_prop α hA hB) (Bool.cond_rec_prop α hB hA)
  have hXe : ∀ m, d ≤ m → ∀ γ, Q.boundary X m γ = X := fun m hm γ =>
    boundary_eq_self (hdX.trans (by exact_mod_cast hm)) γ
  have hterm (C : LowerSet P) (hC : IsMoleculeIn P C) (γ : Bool) :
      (grayProduct P Q).IsSubmoleculeOf (P.boundary C k γ ×ˢ X)
        ((grayProduct P Q).boundary (C ×ˢ X) (n - 1) γ) := by
    have h := isSubmoleculeOf_prod_boundary_boundary hC hX (show k ≤ n - 1 by omega) γ
    rwa [hXe _ (by omega)] at h
  rcases hp.lt_or_eq_boundary α with ⟨-, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · obtain ⟨-, hAB, hBA⟩ := (isPastingIn_cond_iff α).1 hp
    have hE := boundary_prod_eq_sup_of_split_left (A := B) (B := A) hU.isGlobular hB.isGlobular
      hA.isGlobular hX.isGlobular (show k < n by omega)
      (fun i hi => hp.boundary_eq_of_le_cond α hA.isGlobular hB.isGlobular hi)
      (fun i hi => (((isPastingIn_cond_iff α).1
        (hp.boundary_of_lt_cond α hA.isGlobular hB.isGlobular hi α)).1.symm.trans (sup_comm _ _)))
      (by rw [← hBA, hAB]) (fun i hi =>
        (hp.boundary_eq_boundary_of_lt_cond α hA.isGlobular hB.isGlobular hi α).trans
          (hp.boundary_eq_of_lt_cond α hA.isGlobular hB.isGlobular hi α).symm)
    have hI := boundary_prod_inf_of_split_left (A := B) (B := A) hB.isGlobular hA.isGlobular
      hX.isGlobular (show k < n by omega) (α := α) ((inf_comm B A).trans hAB)
      ((inf_comm B A).trans hBA)
    rw [hXe _ (by omega)] at hE hI
    have hBk : P.boundary B k (!α) = P.boundary A k α := hAB.symm.trans hBA
    exact (isMoleculeIn_boundary_prod_of_split hU hX (hp.isPastingFactorOf α hB hA).isSubmoleculeOf
      (.refl hX) (((isPastingIn_cond_comm α).1 hp).isPastingFactorOf (!α) hA hB).isSubmoleculeOf
      (.refl hX) (isMoleculeIn_prod hB hX) (isMoleculeIn_prod hA hX) (by omega) α hE.symm hI
      (hterm B hB (!α)) (by rw [hBk]; exact hterm A hA α)
      (isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn α hA hB hX hp (n - 1))
      (isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn (!α) hB hA hX
        ((isPastingIn_cond_comm α).1 hp) (n - 1))).2.2
  · rw [boundary_prod_eq_self (krullDim_boundary_le U k (!α)) hdX (show k + d ≤ n by omega)]
    exact (hterm U hU (!α)).trans
      ((isMoleculeIn_prod hU hX).boundary_isSubmoleculeOf_boundary (by omega) (!α) α)
  · exact .refl ((isMoleculeIn_prod hU hX).boundary n α)

theorem isSubmoleculeOf_boundary_prod_cond_left_of_lt (β : Bool) {k d n : ℕ}
    {A B U : LowerSet P} {X : LowerSet Q} (hA : IsMoleculeIn P A) (hB : IsMoleculeIn P B)
    (hX : IsMoleculeIn Q X) (hdX : krullDim X ≤ d)
    (hp : P.IsPastingIn k (cond β A B) (cond β B A) U) (hn : k + d < n) (γ : Bool) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (B ×ˢ X) n γ)
      ((grayProduct P Q).boundary (U ×ˢ X) n γ) := by
  by_cases h : β = γ
  · subst h
    exact isSubmoleculeOf_boundary_prod_cond_left_of_isPastingIn β hA hB hX hp n
  · obtain rfl : β = !γ := by cases β <;> cases γ <;> simp at h ⊢
    refine isSubmoleculeOf_boundary_prod_cond_not_left γ hB hA hX hdX ?_ hn
    rwa [isPastingIn_cond_comm, Bool.not_not] at hp

theorem isSubmoleculeOf_boundary_prod_sup_left {k d n : ℕ} {α : Bool} {W D : LowerSet P}
    {X : LowerSet Q} (hW : IsMoleculeIn P W) (hdD : krullDim D ≤ k)
    (hWD : W ⊓ D = P.boundary W k (!α)) (hsub : P.IsSubmoleculeOf (P.boundary W k (!α)) D)
    (hX : IsMoleculeIn Q X) (hdX : krullDim X ≤ d) (hn : k + d ≤ n) (γ : Bool) :
    (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (W ×ˢ X) n γ)
      ((grayProduct P Q).boundary ((W ⊔ D) ×ˢ X) n γ) := by
  refine IsSubmoleculeOf.induction_paste (motive := fun Z E => Z = P.boundary W k (!α) → E ≤ D →
      (grayProduct P Q).IsSubmoleculeOf ((grayProduct P Q).boundary (W ×ˢ X) n γ)
        ((grayProduct P Q).boundary ((W ⊔ E) ×ˢ X) n γ)) ?_ ?_ hsub rfl le_rfl
  · rintro E - rfl -
    rw [sup_eq_left.2 (boundary_le W k (!α))]
    exact .refl ((isMoleculeIn_prod hW hX).boundary n γ)
  · rintro α' k' A B E Z hp mA mB hkB hAE hBE hZA ih rfl hED
    have hdA : krullDim A ≤ k := (LowerSet.krullDim_mono (hAE.trans hED)).trans hdD
    have hWA : W ⊓ A = P.boundary W k (!α) := le_antisymm
      (hWD ▸ inf_le_inf_left W (hAE.trans hED)) (le_inf (boundary_le W k (!α)) hZA.le)
    obtain ⟨mWA, -, -, hbWA, -⟩ := isMoleculeIn_sup_of_isSubmoleculeOf_boundary_boundary
      (α := α) mA hW (by rwa [boundary_eq_self hdA]) ((inf_comm A W).trans hWA)
    rw [boundary_eq_self hdA, sup_comm A W] at hbWA
    rw [sup_comm A W] at mWA
    have hk' : k' < k := by
      have := (LowerSet.krullDim_mono (hBE.trans hED)).trans hdD
      exact_mod_cast hkB.trans_le this
    obtain ⟨hs, hAB, hBA⟩ := (isPastingIn_cond_iff α').1 hp
    have hWB : W ⊓ B ≤ A ⊓ B := le_inf
      ((le_inf inf_le_left (inf_le_right.trans (hBE.trans hED))).trans (hWD.le.trans hZA.le))
      inf_le_right
    have hinf : (W ⊔ A) ⊓ B = A ⊓ B := by
      rw [inf_sup_right, sup_eq_right.2 hWB]
    have hp' : P.IsPastingIn k' (cond α' (W ⊔ A) B) (cond α' B (W ⊔ A)) (W ⊔ E) :=
      (isPastingIn_cond_iff α').2 ⟨by rw [sup_assoc, hs], hinf.trans hAB, by
        rw [hinf, hBA, ← mWA.isGlobular k' k hk' α' (!α), hbWA]⟩
    exact (ih rfl (hAE.trans hED)).trans
      (isSubmoleculeOf_boundary_prod_cond_left_of_lt (!α') mB mWA hX hdX
        ((isPastingIn_cond_comm α').1 hp') (by omega) γ)

theorem isGenPastingIn_cond (α : Bool) {R : OGP.{u}} {k : ℕ} {A B : LowerSet R}
    (hA : IsMoleculeIn R A) (hB : IsMoleculeIn R B)
    (h1 : R.IsSubmoleculeOf (A ⊓ B) (R.boundary A k (!α)))
    (h2 : R.IsSubmoleculeOf (A ⊓ B) (R.boundary B k α))
    (h3 : R.IsSubmoleculeOf (R.boundary A k α) (R.boundary (A ⊔ B) k α))
    (h4 : R.IsSubmoleculeOf (R.boundary B k (!α)) (R.boundary (A ⊔ B) k (!α))) :
    R.IsGenPastingIn k (cond α B A) (cond α A B) := by
  cases α
  · exact ⟨hA, hB, h1, h2, h3, h4⟩
  · exact ⟨hB, hA, inf_comm A B ▸ h2, inf_comm A B ▸ h1, sup_comm A B ▸ h4, sup_comm A B ▸ h3⟩

theorem isGenPastingIn_boundary_prod {U : LowerSet P} {V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) {n j : ℕ} (hj : j < n) (α : Bool) :
    (grayProduct P Q).IsGenPastingIn (n - 1)
      (cond α ((grayProduct P Q).boundary
          (U ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) n α)
        ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α))
      (cond α ((grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α)
        ((grayProduct P Q).boundary
          (U ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) n α)) := by
  have mU := hU.boundary j α
  have mV := hV.boundary (n - j - 1) (xor (j + 1).bodd α)
  have hn1 : n - 1 < n := by omega
  have hs : xor j.bodd (!α) = xor (j + 1).bodd α := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.xor_not]
  have hUj : P.boundary (P.boundary U j α) j (!α) = P.boundary U j α :=
    boundary_eq_self (krullDim_boundary_le U j α) _
  have hVj (γ : Bool) : Q.boundary (Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) (n - 1 - j) γ =
      Q.boundary V (n - j - 1) (xor (j + 1).bodd α) :=
    boundary_eq_self ((krullDim_boundary_le V _ _).trans (by exact_mod_cast (by omega))) γ
  have hpar : xor (n - 1 + (n - j - 1)).bodd (!α) = xor (j + 1).bodd α := by
    rw [show n - 1 + (n - j - 1) = j + 2 * (n - j - 1) by omega, ← hs]
    simp [Nat.bodd_add]
  refine isGenPastingIn_cond α ((isMoleculeIn_prod mU hV).boundary n α)
    ((isMoleculeIn_prod hU mV).boundary n α) ?_ ?_ ?_ ?_
  · rw [boundary_prod_inf hU.isGlobular hV.isGlobular hj,
      isGlobular_prod mU.isGlobular hV.isGlobular (n - 1) n hn1 (!α) α]
    have h := isSubmoleculeOf_prod_boundary_boundary mU hV (show j ≤ n - 1 by omega) (!α)
    rwa [hUj, hs, show n - 1 - j = n - j - 1 by omega] at h
  · rw [boundary_prod_inf hU.isGlobular hV.isGlobular hj,
      isGlobular_prod hU.isGlobular mV.isGlobular (n - 1) n hn1 α α]
    have h := isSubmoleculeOf_prod_boundary_boundary hU mV (show j ≤ n - 1 by omega) α
    rwa [hVj] at h
  · rw [← boundary_prod_eq_sup hU.isGlobular hV.isGlobular hj,
      isGlobular_prod mU.isGlobular hV.isGlobular (n - 1) n hn1 α α,
      isGlobular_prod hU.isGlobular hV.isGlobular (n - 1) n hn1 α α]
    exact isSubmoleculeOf_boundary_prod_boundary_left hU hV (n - 1) j α
  · rw [← boundary_prod_eq_sup hU.isGlobular hV.isGlobular hj,
      isGlobular_prod hU.isGlobular mV.isGlobular (n - 1) n hn1 (!α) α,
      isGlobular_prod hU.isGlobular hV.isGlobular (n - 1) n hn1 (!α) α, ← hpar]
    exact isSubmoleculeOf_boundary_prod_boundary_right hU hV (n - 1) (n - j - 1) (!α)

section PasteAt

variable {k ℓ : ℕ} {α : Bool} {W U U' : LowerSet P} {V : LowerSet Q}

theorem boundary_prod_eq_prod_sup_of_le (hgU : P.IsGlobular U) (hgU' : P.IsGlobular U')
    (hgV : Q.IsGlobular V)
    (p1 : ∀ i ≤ k, P.boundary U' i (!α) = P.boundary U i (!α))
    (p2 : ∀ i, k < i → P.boundary U' i (!α) = W ⊔ P.boundary U i (!α)) :
    (grayProduct P Q).boundary (U' ×ˢ V) (k + 1 + ℓ) (!α) =
      W ×ˢ Q.boundary V ℓ (xor (k + 1).bodd (!α)) ⊔
        (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (!α) := by
  refine SetLike.ext fun ⟨x, y⟩ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, hi, hx, hy⟩ := (mem_boundary_prod_of_isGlobular hgU' hgV).1 h
    by_cases hik : i ≤ k
    · rw [p1 i hik] at hx
      exact Or.inr ((mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, hx, hy⟩)
    · rw [p2 i (by omega)] at hx
      rcases hx with hx | hx
      · refine Or.inl ⟨hx, ?_⟩
        rcases eq_or_lt_of_le (show k + 1 ≤ i by omega) with rfl | hlt
        · rwa [show k + 1 + ℓ - (k + 1) = ℓ by omega] at hy
        · exact hgV.boundary_le_boundary (by omega) _ _ hy
      · exact Or.inr ((mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, hx, hy⟩)
  · refine (mem_boundary_prod_of_isGlobular hgU' hgV).2 ?_
    rcases h with ⟨hx, hy⟩ | h
    · refine ⟨k + 1, by omega, by rw [p2 _ (by omega)]; exact Or.inl hx, ?_⟩
      rwa [show k + 1 + ℓ - (k + 1) = ℓ by omega]
    · obtain ⟨i, hi, hx, hy⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
      refine ⟨i, hi, ?_, hy⟩
      by_cases hik : i ≤ k
      · rwa [p1 i hik]
      · rw [p2 i (by omega)]; exact Or.inr hx

theorem prod_inf_boundary_prod (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V)
    (hWU : W ⊓ U ≤ P.boundary U k α) :
    W ×ˢ Q.boundary V ℓ (xor (k + 1).bodd (!α)) ⊓
        (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (!α) =
      (W ⊓ U) ×ˢ Q.boundary V ℓ (xor (k + 1).bodd (!α)) := by
  refine SetLike.ext fun ⟨x, y⟩ => ⟨fun ⟨⟨hxW, hy⟩, h⟩ => ?_, fun ⟨⟨hxW, hxU⟩, hy⟩ => ?_⟩
  · obtain ⟨i, -, hx, -⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    exact ⟨⟨hxW, boundary_le U i _ hx⟩, hy⟩
  · refine ⟨⟨hxW, hy⟩, (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨k + 1, by omega,
      hgU.boundary_le_boundary (Nat.lt_succ_self k) α (!α) (hWU ⟨hxW, hxU⟩), ?_⟩⟩
    rwa [show k + 1 + ℓ - (k + 1) = ℓ by omega]

end PasteAt

theorem isPastingAtIn_dual_bodd {k : ℕ} {α : Bool} {W V : LowerSet Q}
    (hc : Q.IsPastingAtIn k α W V (W ⊔ V)) :
    (OGP.dual Q Nat.bodd).IsPastingAtIn k (xor (k + 1).bodd α) W V (W ⊔ V) :=
  (isPastingAtIn_dual Nat.bodd).2 (by rwa [Bool.xor_xor_cancel_left])

theorem boundary_prod_pasteAt_right {k ℓ : ℕ} {α : Bool} {W V : LowerSet Q}
    {U : LowerSet P} (hU : IsMoleculeIn P U) (hdW : Order.krullDim W ≤ (k + 1 : ℕ))
    (hc : Q.IsPastingAtIn k α W V (W ⊔ V)) :
    (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + 1 + ℓ) (xor ℓ.bodd α) =
      P.boundary U ℓ (xor ℓ.bodd α) ×ˢ W ⊔
        (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + ℓ) (xor ℓ.bodd α) := by
  have hc' := isPastingAtIn_dual_bodd hc
  have hV' := hc'.isMoleculeIn_right
  have hU' := hc'.isMoleculeIn
  have h := congrArg (OGP.map (grayProductSwap P Q).inv) (boundary_prod_eq_prod_sup_of_le (ℓ := ℓ)
    hV'.isGlobular hU'.isGlobular ((isMoleculeIn_dual Nat.bodd).2 hU).isGlobular
    (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · rw [← hU'.isGlobular i k hi _ _, hc'.boundary_not, hV'.isGlobular i k hi _ _]
      · exact hc'.boundary_not)
    (fun i hi => hc'.boundary_eq_sup_of_lt hi (hdW.trans (by exact_mod_cast hi)) _))
  rw [OGP.map_sup] at h
  simp only [map_grayProductSwap_inv_boundary_prod, map_grayProductSwap_inv_prod,
    boundary_dual] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

theorem isMolecule_grayProduct (hP : IsMolecule P) (hQ : IsMolecule Q) :
    IsMolecule (grayProduct P Q) := by
  have h := isMoleculeIn_prod hP hQ
  rwa [LowerSet.top_prod_top] at h

theorem isAtomIn_prod {U : LowerSet P} {V : LowerSet Q} (hU : P.IsAtomIn U) (hV : Q.IsAtomIn V) :
    (grayProduct P Q).IsAtomIn (U ×ˢ V) := by
  obtain ⟨t, rfl⟩ := hU.exists_eq_Iic
  obtain ⟨t', rfl⟩ := hV.exists_eq_Iic
  exact ⟨isMoleculeIn_prod hU.isMoleculeIn hV.isMoleculeIn, (t, t'), (Iic_grayProduct t t').symm⟩

theorem isAtom_grayProduct (hP : IsAtom P) (hQ : IsAtom Q) :
    IsAtom (grayProduct P Q) := by
  have h := isAtomIn_prod hP hQ
  rwa [LowerSet.top_prod_top] at h

theorem isAtom_cube (n : ℕ) : IsAtom (cube.{u} n) := by
  induction n with
  | zero => exact isAtom_point
  | succ n ih => exact isAtom_grayProduct (isAtom_globe 1) ih

theorem isRDC_cube (n : ℕ) : IsRDC (cube.{u} n) :=
  isRDC_of_isMolecule (isAtom_cube n).1

def grayProductRestrictIso (S : LowerSet P) (T : LowerSet Q) :
    (grayProduct P Q).restrict (S ×ˢ T) ≅ grayProduct (P.restrict S) (Q.restrict T) :=
  isoMk ⟨Equiv.Set.prod (S : Set P) (T : Set Q), Iff.rfl⟩ fun _ => rfl

@[simp] theorem grayProductRestrictIso_hom_apply (S : LowerSet P) (T : LowerSet Q)
    (x : (grayProduct P Q).restrict (S ×ˢ T)) :
    (((grayProductRestrictIso S T).hom x).1.1, ((grayProductRestrictIso S T).hom x).2.1) = x.1 :=
  rfl

def grayProductClosureIso (p : P) (q : Q) :
    (grayProduct P Q).restrict (.Iic (p, q)) ≅
      grayProduct (P.restrict (.Iic p)) (Q.restrict (.Iic q)) :=
  (restrictCongr (Iic_grayProduct p q)).trans (grayProductRestrictIso (.Iic p) (.Iic q))

@[simp] theorem grayProductClosureIso_hom_apply (p : P) (q : Q)
    (x : (grayProduct P Q).restrict (.Iic (p, q))) :
    (((grayProductClosureIso p q).hom x).1.1, ((grayProductClosureIso p q).hom x).2.1) = x.1 :=
  rfl

theorem isRDC_grayProduct (hP : IsRDC P) (hQ : IsRDC Q) : IsRDC (grayProduct P Q) :=
  fun ⟨p, q⟩ => Iic_grayProduct p q ▸ isMoleculeIn_prod (hP p) (hQ q)

end Atoms.Molecule.OGP
