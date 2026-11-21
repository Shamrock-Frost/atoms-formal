import Atoms.ForMathlib.Data.Bool.Basic
import Atoms.ForMathlib.Data.Nat.Bits
import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.Construction.Basic
import Atoms.Molecule.Pasting.Basic
import Mathlib.Order.UpperLower.Prod

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

theorem grayProduct_orient_of_covBy_fst {x x' : P} (h : x' ⋖ x) (y : Q)
    (hpq : ((x', y) : grayProduct P Q) ⋖ (x, y)) :
    (grayProduct P Q).orient hpq = P.orient h := by
  change (if hg : _ then _ else _) = _
  rw [dif_neg (grade_strictMono h.lt).ne]

theorem grayProduct_orient_of_covBy_snd (x : P) {y y' : Q} (h : y' ⋖ y)
    (hpq : ((x, y') : grayProduct P Q) ⋖ (x, y)) :
    (grayProduct P Q).orient hpq = xor (grade ℕ x).bodd (Q.orient h) := by
  change (if hg : _ then _ else _) = _
  rw [dif_pos rfl]

theorem mem_cofaces_grayProduct {β : Bool} {p q : grayProduct P Q} :
    q ∈ (grayProduct P Q).cofaces β p ↔
      q.1 ∈ P.cofaces β p.1 ∧ q.2 = p.2 ∨
        q.1 = p.1 ∧ q.2 ∈ Q.cofaces (xor (grade ℕ p.1).bodd β) p.2 := by
  change p ∈ (grayProduct P Q).faces β q ↔
    p.1 ∈ P.faces β q.1 ∧ q.2 = p.2 ∨
      q.1 = p.1 ∧ p.2 ∈ Q.faces (xor (grade ℕ p.1).bodd β) q.2
  rw [mem_faces_grayProduct]
  exact or_congr (and_congr_right fun _ => eq_comm)
    (and_congr_left' eq_comm |>.trans (and_congr_right fun h => by rw [h]))

variable (P Q) in
def grayProductSwap :
    dual (grayProduct P Q) Nat.bodd ≅ grayProduct (dual Q Nat.bodd) (dual P Nat.bodd) :=
  isoMk OrderIso.prodComm fun {p q} h => by
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    rcases Prod.covBy_iff.1 h with ⟨hx, hyy⟩ | ⟨hy, hxx⟩
    · obtain rfl : y' = y := hyy
      replace hx : x' ⋖ x := hx
      have h' : ((y', x') : grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)) ⋖ (y', x) :=
        Prod.covBy_iff.2 (.inr ⟨hx, rfl⟩)
      rw [orient_congr _ _ _ h', grayProduct_orient_of_covBy_snd (P := dual Q Nat.bodd)
        (Q := dual P Nat.bodd) y' hx, orient_dual, orient_dual,
        grayProduct_orient_of_covBy_fst hx y' h, Prod.grade_eq_add, Nat.bodd_add, Bool.xor_assoc]
      · exact Bool.xor_left_comm _ _ _
      · rfl
      · rfl
    · obtain rfl : x' = x := hxx
      replace hy : y' ⋖ y := hy
      have h' : ((y', x') : grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)) ⋖ (y, x') :=
        Prod.covBy_iff.2 (.inl ⟨hy, rfl⟩)
      rw [orient_congr _ _ _ h', grayProduct_orient_of_covBy_fst (P := dual Q Nat.bodd)
        (Q := dual P Nat.bodd) hy x', orient_dual, orient_dual,
        grayProduct_orient_of_covBy_snd x' hy h, Prod.grade_eq_add, Nat.bodd_add, Bool.xor_assoc,
        Bool.xor_left_comm, Bool.xor_xor_cancel_left]
      · rfl
      · rfl

theorem map_grayProductSwap_inv_prod (U : LowerSet P) (V : LowerSet Q) :
    map (grayProductSwap P Q).inv
        (V ×ˢ U : LowerSet (grayProduct (dual Q Nat.bodd) (dual P Nat.bodd))) =
      (U ×ˢ V : LowerSet (grayProduct P Q)) :=
  SetLike.coe_injective (by
    rw [coe_map, LowerSet.coe_prod, LowerSet.coe_prod]
    exact Set.image_swap_prod _ _)

theorem map_grayProductSwap_inv_boundary_prod (U : LowerSet P) (V : LowerSet Q) (n : ℕ)
    (α : Bool) :
    map (grayProductSwap P Q).inv ((grayProduct (dual Q Nat.bodd) (dual P Nat.bodd)).boundary
        (V ×ˢ U) n α) =
      (grayProduct P Q).boundary (U ×ˢ V) n (xor (n + 1).bodd α) := by
  rw [map_boundary, map_grayProductSwap_inv_prod]
  exact boundary_dual _ _ n α

theorem krullDim_prod_le {U : LowerSet P} {V : LowerSet Q} {m n : ℕ}
    (hU : krullDim U ≤ m) (hV : krullDim V ≤ n) :
    krullDim ↥(U ×ˢ V : LowerSet (grayProduct P Q)) ≤ (m + n : ℕ) :=
  krullDim_le_coe_iff.2 fun p =>
    Nat.add_le_add (krullDim_le_coe_iff.1 hU ⟨p.1.1, p.2.1⟩)
      (krullDim_le_coe_iff.1 hV ⟨p.1.2, p.2.2⟩)

theorem krullDim_prod {U : LowerSet P} {V : LowerSet Q} {m n : ℕ}
    (hU : krullDim U = m) (hV : krullDim V = n) :
    krullDim ↥(U ×ˢ V : LowerSet (grayProduct P Q)) = (m + n : ℕ) := by
  refine le_antisymm (krullDim_prod_le hU.le hV.le) ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := exists_grade_eq_of_krullDim_eq hU
  obtain ⟨⟨y, hy⟩, rfl⟩ := exists_grade_eq_of_krullDim_eq hV
  exact grade_le_krullDim (⟨(x, y), ⟨hx, hy⟩⟩ : ↥(U ×ˢ V : LowerSet (grayProduct P Q)))

theorem krullDim_grayProduct {m n : ℕ} (hP : krullDim P = m) (hQ : krullDim Q = n) :
    krullDim (grayProduct P Q) = (m + n : ℕ) := by
  rw [← LowerSet.krullDim_top, ← LowerSet.top_prod_top]
  exact krullDim_prod (by rwa [LowerSet.krullDim_top]) (by rwa [LowerSet.krullDim_top])

theorem bdry_grayProduct_top {m n : ℕ} (hP : krullDim P = m) (hQ : krullDim Q = n)
    (hd : 0 < m + n) (α : Bool) :
    (grayProduct P Q).bdry ⊤ α = (grayProduct P Q).boundary ⊤ (m + n - 1) α := by
  refine bdry_eq_boundary ?_ α
  rw [LowerSet.krullDim_top, krullDim_grayProduct hP hQ]
  exact_mod_cast congrArg (Nat.cast (R := WithBot ℕ∞)) (Nat.sub_add_cancel hd).symm

theorem mem_facesIn_prod {U : LowerSet P} {V : LowerSet Q} {n : ℕ} {α : Bool} {x : P} {y : Q} :
    ((x, y) : grayProduct P Q) ∈
        (grayProduct P Q).facesIn (U ×ˢ V : LowerSet (grayProduct P Q)) n α ↔
      grade ℕ x + grade ℕ y = n ∧
        x ∈ P.facesIn U (grade ℕ x) α ∧ y ∈ Q.facesIn V (grade ℕ y) (xor (grade ℕ x).bodd α) := by
  have hs := Bool.xor_not (grade ℕ x).bodd α
  simp only [facesIn, mem_ofPred_eq, SetLike.mem_coe, LowerSet.mem_prod, Prod.grade_eq_add,
    disjoint_left, true_and]
  constructor
  · rintro ⟨⟨hxU, hyV⟩, hn, h⟩
    refine ⟨hn,
      ⟨hxU, fun a hc haU =>
        h (mem_cofaces_grayProduct (p := (x, y)) (q := (a, y)).2 (Or.inl ⟨hc, rfl⟩)) ⟨haU, hyV⟩⟩,
      ⟨hyV, fun b hc hbV =>
        h (mem_cofaces_grayProduct (p := (x, y)) (q := (x, b)).2 (Or.inr ⟨rfl, by rwa [hs]⟩))
          ⟨hxU, hbV⟩⟩⟩
  · rintro ⟨hn, ⟨hxU, hU⟩, ⟨hyV, hV⟩⟩
    refine ⟨⟨hxU, hyV⟩, hn, fun ⟨a, b⟩ hc ⟨haU, hbV⟩ => ?_⟩
    rcases mem_cofaces_grayProduct.1 hc with ⟨hc, rfl⟩ | ⟨rfl, hc⟩
    · exact hU hc haU
    · rw [hs] at hc
      exact hV hc hbV

theorem maximal_mem_prod_iff {U : LowerSet P} {V : LowerSet Q} {x : P} {y : Q} :
    Maximal (· ∈ (U ×ˢ V : LowerSet (grayProduct P Q))) ((x, y) : grayProduct P Q) ↔
      Maximal (· ∈ U) x ∧ Maximal (· ∈ V) y :=
  ⟨fun h => ⟨⟨h.prop.1, fun a ha hxa => (@h.2 (a, y) ⟨ha, h.prop.2⟩ ⟨hxa, le_rfl⟩).1⟩,
    ⟨h.prop.2, fun b hb hyb => (@h.2 (x, b) ⟨h.prop.1, hb⟩ ⟨le_rfl, hyb⟩).2⟩⟩,
  fun ⟨hx, hy⟩ => ⟨⟨hx.prop, hy.prop⟩, fun _ hab hle => ⟨hx.2 hab.1 hle.1, hy.2 hab.2 hle.2⟩⟩⟩

theorem boundary_prod_le (U : LowerSet P) (V : LowerSet Q) (n : ℕ) (α : Bool) :
    (grayProduct P Q).boundary (U ×ˢ V) n α ≤
      ⨆ k ≤ n, P.boundary U k α ×ˢ Q.boundary V (n - k) (xor k.bodd α) := by
  rintro ⟨x, y⟩ hz
  obtain ⟨⟨a, b⟩, hg, hle⟩ := mem_boundary.1 hz
  change (x, y) ∈ (⨆ k ≤ n, P.boundary U k α ×ˢ Q.boundary V (n - k) (xor k.bodd α) :
    LowerSet (grayProduct P Q))
  rw [LowerSet.mem_iSup₂_iff]
  rcases hg with hf | ⟨hm, hd⟩
  · obtain ⟨hd, hfa, hfb⟩ := mem_facesIn_prod.1 hf
    exact ⟨grade ℕ a, by omega, mem_boundary_of_mem_facesIn hfa hle.1,
      mem_boundary_of_mem_facesIn (by convert hfb using 2; omega) hle.2⟩
  · obtain ⟨hma, hmb⟩ := maximal_mem_prod_iff.1 hm
    change grade ℕ a + grade ℕ b < n at hd
    exact ⟨grade ℕ a, by omega,
      mem_boundary_of_mem_facesIn (maximal_mem_iff_forall_mem_facesIn.1 hma α) hle.1,
      mem_boundary_of_maximal hmb (by omega) hle.2⟩

theorem mem_boundary_prod_of_maximal_left {U : LowerSet P} {V : LowerSet Q} {n : ℕ} {α : Bool}
    {x : P} {y : Q} (hx : Maximal (· ∈ U) x) (hn : grade ℕ x ≤ n)
    (hy : y ∈ Q.boundary V (n - grade ℕ x) (xor (grade ℕ x).bodd α)) :
    ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundary (U ×ˢ V) n α := by
  obtain ⟨b, hb, hyb⟩ := mem_boundary.1 hy
  rcases hb with hbf | ⟨hbm, hbd⟩
  · have hdb : grade ℕ b = n - grade ℕ x := hbf.2.1
    exact mem_boundary_of_mem_facesIn (z := (x, b))
      (mem_facesIn_prod.2 ⟨by omega, maximal_mem_iff_forall_mem_facesIn.1 hx α, by rwa [hdb]⟩)
      ⟨le_rfl, hyb⟩
  · exact mem_boundary_of_maximal (z := (x, b)) (maximal_mem_prod_iff.2 ⟨hx, hbm⟩)
      (by change grade ℕ x + grade ℕ b < n; omega) ⟨le_rfl, hyb⟩

theorem mem_boundary_prod_of_maximal_right {U : LowerSet P} {V : LowerSet Q} {n : ℕ} {α : Bool}
    {x : P} {y : Q} (hy : Maximal (· ∈ V) y) (hn : grade ℕ y ≤ n)
    (hx : x ∈ P.boundary U (n - grade ℕ y) α) :
    ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundary (U ×ˢ V) n α := by
  obtain ⟨a, ha, hxa⟩ := mem_boundary.1 hx
  rcases ha with haf | ⟨ham, had⟩
  · have hda : grade ℕ a = n - grade ℕ y := haf.2.1
    exact mem_boundary_of_mem_facesIn (z := (a, y))
      (mem_facesIn_prod.2 ⟨by omega, by rwa [hda], maximal_mem_iff_forall_mem_facesIn.1 hy _⟩)
      ⟨hxa, le_rfl⟩
  · exact mem_boundary_of_maximal (z := (a, y)) (maximal_mem_prod_iff.2 ⟨ham, hy⟩)
      (by change grade ℕ a + grade ℕ y < n; omega) ⟨hxa, le_rfl⟩

theorem mem_boundary_prod_of_isGlobular {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n : ℕ} {α : Bool} {x : P} {y : Q} :
    ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundary (U ×ˢ V) n α ↔
      ∃ k ≤ n, x ∈ P.boundary U k α ∧ y ∈ Q.boundary V (n - k) (xor k.bodd α) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, hk, hxy⟩ := LowerSet.mem_iSup₂_iff.1 (boundary_prod_le U V n α h)
    exact ⟨k, hk, hxy.1, hxy.2⟩
  · rintro ⟨k, hk, hx, hy⟩
    obtain ⟨a, ha, hxa⟩ := mem_boundary.1 hx
    obtain ⟨b, hb, hyb⟩ := mem_boundary.1 hy
    have hbmem : b ∈ Q.boundary V (n - k) (xor k.bodd α) := mem_boundary.2 ⟨b, hb, le_rfl⟩
    have hamem : a ∈ P.boundary U k α := mem_boundary.2 ⟨a, ha, le_rfl⟩
    refine LowerSet.lower _ (a := (a, b)) ⟨hxa, hyb⟩ ?_
    rcases ha with haf | ⟨ham, had⟩
    · have hda : grade ℕ a = k := haf.2.1
      rcases hb with hbf | ⟨hbm, hbd⟩
      · have hdb : grade ℕ b = n - k := hbf.2.1
        exact mem_boundary_of_mem_facesIn (z := (a, b))
          (mem_facesIn_prod.2 ⟨by omega, by rwa [hda], by rwa [hda, hdb]⟩) le_rfl
      · exact mem_boundary_prod_of_maximal_right hbm (by omega)
          (hgU.boundary_le_boundary (by omega : k < n - grade ℕ b) α α hamem)
    · exact mem_boundary_prod_of_maximal_left ham (by omega)
        (hgV.boundary_le_boundary (by omega : n - k < n - grade ℕ a) _ _ hbmem)

theorem boundary_prod_of_isGlobular {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) (n : ℕ) (α : Bool) :
    (grayProduct P Q).boundary (U ×ˢ V) n α =
      ⨆ k ≤ n, P.boundary U k α ×ˢ Q.boundary V (n - k) (xor k.bodd α) :=
  SetLike.ext fun ⟨x, y⟩ => by
    rw [mem_boundary_prod_of_isGlobular hgU hgV, LowerSet.mem_iSup₂_iff]
    simp only [LowerSet.mem_prod, exists_prop]

theorem boundary_Iic_grayProduct_zero {x : P} {y : Q}
    (hx : P.IsGlobular (.Iic x)) (hy : Q.IsGlobular (.Iic y)) (α : Bool) :
    (grayProduct P Q).boundary (.Iic (x, y)) 0 α =
      P.boundary (.Iic x) 0 α ×ˢ Q.boundary (.Iic y) 0 α :=
  SetLike.ext fun ⟨a, b⟩ => by
    rw [LowerSet.Iic_prod]
    change ((a, b) : grayProduct P Q) ∈
      (grayProduct P Q).boundary (LowerSet.Iic x ×ˢ LowerSet.Iic y) 0 α ↔ _
    rw [mem_boundary_prod_of_isGlobular hx hy]
    simp

private theorem IsGlobular.boundary_le_boundary_of_le {U : LowerSet P} (hg : P.IsGlobular U)
    {k n : ℕ} (h : k ≤ n) (α : Bool) : P.boundary U k α ≤ P.boundary U n α := by
  rcases h.lt_or_eq with h | rfl
  · exact hg.boundary_le_boundary h α α
  · exact le_rfl

private theorem IsGlobular.boundary_le_boundary_of_lt_or_eq {U : LowerSet P} (hg : P.IsGlobular U)
    {k n : ℕ} {α β : Bool} (h : k < n ∨ k = n ∧ α = β) :
    P.boundary U k α ≤ P.boundary U n β := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact hg.boundary_le_boundary h α β
  · exact le_rfl

private theorem IsGlobular.boundary_boundary_le {U : LowerSet P} (hg : P.IsGlobular U)
    {k n : ℕ} {α β : Bool} (h : k < n ∨ α = β) :
    P.boundary (P.boundary U n β) k α ≤ P.boundary U k α := by
  rcases lt_or_ge k n with hlt | hge
  · exact (hg k n hlt α β).le
  · obtain rfl : α = β := h.resolve_left hge.not_gt
    rw [boundary_boundary_of_le hge]
    exact hg.boundary_le_boundary_of_le hge α

private theorem mem_facesIn_of_mem_facesIn_boundary_prod {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n k j : ℕ} (hj : j ≤ n) {α β : Bool}
    {x : P} {y : Q}
    (hf : ((x, y) : grayProduct P Q) ∈
      (grayProduct P Q).facesIn ((grayProduct P Q).boundary (U ×ˢ V) n β) k α)
    (hx : x ∈ P.boundary U j β) (hy : y ∈ Q.boundary V (n - j) (xor j.bodd β)) :
    (grade ℕ x < j → x ∈ P.facesIn U (grade ℕ x) α) ∧
      (grade ℕ y < n - j → y ∈ Q.facesIn V (grade ℕ y) (xor (grade ℕ x).bodd α)) := by
  have hsub : ((P.boundary U j β ×ˢ Q.boundary V (n - j) (xor j.bodd β) :
      LowerSet (grayProduct P Q)) : Set (grayProduct P Q)) ⊆
      (grayProduct P Q).boundary (U ×ˢ V) n β := fun ⟨a, b⟩ hab =>
    (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨j, hj, hab.1, hab.2⟩
  have piece := (mem_facesIn_prod.1 (mem_facesIn_of_subset hsub hf ⟨hx, hy⟩)).2
  refine ⟨fun hdj => ?_, fun hdj => ?_⟩
  · rw [← facesIn_eq_of_boundary_eq (hgU (grade ℕ x) j hdj α β)]
    exact piece.1
  · rw [← facesIn_eq_of_boundary_eq (hgV (grade ℕ y) (n - j) hdj _ _)]
    exact piece.2

private theorem mem_facesIn_prod_of_mem_facesIn_boundary_prod {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n k : ℕ} (hk : k < n) {α β : Bool}
    {x : P} {y : Q}
    (hf : ((x, y) : grayProduct P Q) ∈
      (grayProduct P Q).facesIn ((grayProduct P Q).boundary (U ×ˢ V) n β) k α) :
    ((x, y) : grayProduct P Q) ∈
      (grayProduct P Q).facesIn (U ×ˢ V : LowerSet (grayProduct P Q)) k α := by
  have hβ' : β ≠ α → β = !α := Bool.eq_not_iff.2
  have hd : grade ℕ x + grade ℕ y = k := hf.2.1
  obtain ⟨j0, hj0, hx0, hy0⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 hf.1
  have part {j : ℕ} (hj : j ≤ n) (hx : x ∈ P.boundary U j β)
      (hy : y ∈ Q.boundary V (n - j) (xor j.bodd β)) :=
    mem_facesIn_of_mem_facesIn_boundary_prod hgU hgV hj hf hx hy
  have hdx0 : grade ℕ x ≤ j0 := grade_le_of_mem_boundary hx0
  have hey0 : grade ℕ y ≤ n - j0 := grade_le_of_mem_boundary hy0
  refine mem_facesIn_prod.2 ⟨hd, ?_⟩
  rcases eq_or_lt_of_le hdx0 with hd0 | hd0
  · have hyf := (part hj0 hx0 hy0).2 (by omega)
    refine ⟨?_, hyf⟩
    by_cases hβ : β = α
    · subst hβ
      exact hd0 ▸ mem_facesIn_of_mem_boundary hx0 hd0
    · have hx1 : x ∈ P.boundary U (j0 + 1) β :=
        hgU.boundary_le_boundary (Nat.lt_succ_self j0) β β hx0
      have hy1 : y ∈ Q.boundary V (n - (j0 + 1)) (xor (j0 + 1).bodd β) := by
        rw [hβ' hβ, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, ← hd0]
        exact hgV.boundary_le_boundary_of_le (by omega) _
          (mem_boundary_of_mem_facesIn hyf le_rfl)
      exact (part (by omega) hx1 hy1).1 (by omega)
  · have hxf := (part hj0 hx0 hy0).1 hd0
    refine ⟨hxf, ?_⟩
    rcases eq_or_lt_of_le hey0 with he0 | he0
    · have hyf : y ∈ Q.facesIn V (grade ℕ y) (xor j0.bodd β) :=
        he0 ▸ mem_facesIn_of_mem_boundary hy0 he0
      by_cases hs : xor j0.bodd β = xor (grade ℕ x).bodd α
      · rwa [← hs]
      · have hxd : x ∈ P.boundary U (grade ℕ x) α := mem_boundary_of_mem_facesIn hxf le_rfl
        have hx1 : x ∈ P.boundary U (j0 - 1) β := by
          rcases eq_or_lt_of_le (show grade ℕ x ≤ j0 - 1 by omega) with h | h
          · have hβα : β = α := by
              by_contra hne
              apply hs
              rw [hβ' hne, show j0 = grade ℕ x + 1 by omega, Nat.bodd_succ,
                Bool.not_xor, Bool.xor_not, Bool.not_not]
            rwa [hβα, ← h]
          · exact hgU.boundary_le_boundary h α β hxd
        have hy1 : y ∈ Q.boundary V (n - (j0 - 1)) (xor (j0 - 1).bodd β) :=
          hgV.boundary_le_boundary (by omega : n - j0 < n - (j0 - 1)) _ _ hy0
        exact (part (by omega) hx1 hy1).2 (by omega)
    · exact (part hj0 hx0 hy0).2 he0

private theorem mem_boundary_prod_of_mem_facesIn_prod {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n k : ℕ} (hk : k < n) {α : Bool} (β : Bool)
    {x : P} {y : Q}
    (hf : ((x, y) : grayProduct P Q) ∈
      (grayProduct P Q).facesIn (U ×ˢ V : LowerSet (grayProduct P Q)) k α) :
    ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundary (U ×ˢ V) n β := by
  obtain ⟨hd, hxf, hyf⟩ := mem_facesIn_prod.1 hf
  have hxb := mem_boundary_of_mem_facesIn hxf le_rfl
  have hyb := mem_boundary_of_mem_facesIn hyf le_rfl
  by_cases hβ : β = α
  · subst hβ
    exact (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨grade ℕ x, by omega, hxb,
      hgV.boundary_le_boundary_of_le (by omega) _ hyb⟩
  · refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨grade ℕ x + 1, by omega,
      hgU.boundary_le_boundary (Nat.lt_succ_self _) α β hxb, ?_⟩
    rw [Bool.eq_not_iff.2 hβ, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not]
    exact hgV.boundary_le_boundary_of_le (by omega) _ hyb

theorem mem_facesIn_boundary_prod_iff {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n k : ℕ}
    (hk : k < n) (α β : Bool) {x : P} {y : Q} :
    ((x, y) : grayProduct P Q) ∈
        (grayProduct P Q).facesIn ((grayProduct P Q).boundary (U ×ˢ V) n β) k α ↔
      ((x, y) : grayProduct P Q) ∈
        (grayProduct P Q).facesIn (U ×ˢ V : LowerSet (grayProduct P Q)) k α :=
  ⟨mem_facesIn_prod_of_mem_facesIn_boundary_prod hgU hgV hk, fun hf =>
    mem_facesIn_of_subset (boundary_le (P := grayProduct P Q) (U ×ˢ V) n β) hf
      (mem_boundary_prod_of_mem_facesIn_prod hgU hgV hk β hf)⟩

theorem isGlobular_prod {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) :
    (grayProduct P Q).IsGlobular (U ×ˢ V) := by
  intro k n hk α β
  refine boundary_congr (Set.ext fun ⟨x, y⟩ => ?_) fun z hz => ?_
  · exact mem_facesIn_boundary_prod_iff hgU hgV hk α β
  · exact maximal_mem_boundary_iff_of_grade_lt (hz.trans hk)

private theorem mem_boundaryFull_prod_of_mem {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n m : ℕ} (hm : m ≤ n - 1) {γ : Bool}
    {x : P} {y : Q} (hx : x ∈ P.boundary U m γ)
    (hy : y ∈ Q.boundary V (n - 1 - m) (xor m.bodd γ)) :
    ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundaryFull (U ×ˢ V) (n - 1) := by
  have h := (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨m, hm, hx, hy⟩
  rw [boundaryFull]
  cases γ
  exacts [Or.inl h, Or.inr h]

private theorem pos_and_mem_boundaryFull_prod_of_mem_inf {U : LowerSet P} {V : LowerSet Q}
    (hrU : P.IsRound U) (hrV : Q.IsRound V) {n i : ℕ} (hi : i ≤ n)
    (hn : (n : WithBot ℕ∞) < krullDim ↥(U ×ˢ V : LowerSet (grayProduct P Q)))
    {x : P} {y : Q} (hx1 : x ∈ P.boundary U i true) (hx2 : x ∈ P.boundary U i false)
    (hyall : ∀ δ, y ∈ Q.boundary V (n - i) δ) :
    0 < n ∧ ((x, y) : grayProduct P Q) ∈ (grayProduct P Q).boundaryFull (U ×ˢ V) (n - 1) := by
  obtain ⟨p₀, hp₀⟩ := coe_lt_krullDim_iff.1 hn
  change n < grade ℕ p₀.1.1 + grade ℕ p₀.1.2 at hp₀
  by_cases hip : (i : WithBot ℕ∞) < krullDim U
  · cases i with
    | zero =>
      have h0 : 0 < krullDim U := by simpa using hip
      have hx : x ∈ P.boundary U 0 false ⊓ P.boundary U 0 true := ⟨hx2, hx1⟩
      rw [hrU.inf_boundary_zero h0] at hx
      exact hx.elim
    | succ m =>
      have hx : x ∈ P.boundary U (m + 1) false ⊓ P.boundary U (m + 1) true := ⟨hx2, hx1⟩
      rw [hrU.inf_boundary_succ m hip, boundaryFull] at hx
      obtain ⟨γ, h⟩ : ∃ γ, x ∈ P.boundary U m γ := hx.elim (⟨false, ·⟩) (⟨true, ·⟩)
      refine ⟨by omega, mem_boundaryFull_prod_of_mem hrU.isGlobular hrV.isGlobular
        (by omega) h ?_⟩
      rw [show n - 1 - m = n - (m + 1) by omega]
      exact hyall _
  · have hUi : krullDim U ≤ i := not_lt.1 hip
    have hxU : x ∈ U := boundary_le U i true hx1
    have hxall (γ : Bool) : x ∈ P.boundary U i γ := by
      rw [boundary_eq_self hUi]
      exact hxU
    have hp₀1 : grade ℕ p₀.1.1 ≤ i := krullDim_le_coe_iff.1 hUi ⟨p₀.1.1, p₀.2.1⟩
    have hVp : ((n - i : ℕ) : WithBot ℕ∞) < krullDim V :=
      coe_lt_krullDim_iff.2 ⟨⟨p₀.1.2, p₀.2.2⟩, by
        change n - i < grade ℕ p₀.1.2; omega⟩
    cases hni : n - i with
    | zero =>
      rw [hni] at hVp
      have h0 : 0 < krullDim V := by simpa using hVp
      have hy : y ∈ Q.boundary V 0 false ⊓ Q.boundary V 0 true := by
        rw [← hni]; exact ⟨hyall false, hyall true⟩
      rw [hrV.inf_boundary_zero h0] at hy
      exact hy.elim
    | succ m =>
      rw [hni] at hVp
      have hy : y ∈ Q.boundary V (m + 1) false ⊓ Q.boundary V (m + 1) true := by
        rw [← hni]; exact ⟨hyall false, hyall true⟩
      rw [hrV.inf_boundary_succ m hVp, boundaryFull] at hy
      obtain ⟨δ, h⟩ : ∃ δ, y ∈ Q.boundary V m δ := hy.elim (⟨false, ·⟩) (⟨true, ·⟩)
      refine ⟨by omega, mem_boundaryFull_prod_of_mem hrU.isGlobular hrV.isGlobular
        (γ := xor i.bodd δ) (by omega) (hxall _) ?_⟩
      rwa [Bool.xor_xor_cancel_left, show n - 1 - i = m by omega]

private theorem pos_and_mem_boundaryFull_prod {U : LowerSet P} {V : LowerSet Q}
    (hrU : P.IsRound U) (hrV : Q.IsRound V) {n : ℕ}
    (hn : (n : WithBot ℕ∞) < krullDim ↥(U ×ˢ V : LowerSet (grayProduct P Q)))
    {z : grayProduct P Q} (h1 : z ∈ (grayProduct P Q).boundary (U ×ˢ V) n true)
    (h2 : z ∈ (grayProduct P Q).boundary (U ×ˢ V) n false) :
    0 < n ∧ z ∈ (grayProduct P Q).boundaryFull (U ×ˢ V) (n - 1) := by
  have hgU := hrU.isGlobular
  have hgV := hrV.isGlobular
  rcases z with ⟨x, y⟩
  obtain ⟨i, hi, hx1, hy1⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h1
  obtain ⟨j, hj, hx2, hy2⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h2
  rcases lt_trichotomy i j with hij | rfl | hij
  · refine ⟨by omega, mem_boundaryFull_prod_of_mem hgU hgV (by omega) hx1 ?_⟩
    refine hgV.boundary_le_boundary_of_lt_or_eq ?_ hy2
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact Or.inr ⟨by omega, by rw [Nat.bodd_succ]; cases i.bodd <;> rfl⟩
    · exact Or.inl (by omega)
  · refine pos_and_mem_boundaryFull_prod_of_mem_inf hrU hrV hi hn hx1 hx2 fun δ => ?_
    cases δ <;> cases h : i.bodd <;> rw [h] at hy1 hy2 <;> assumption
  · refine ⟨by omega, mem_boundaryFull_prod_of_mem hgU hgV (by omega) hx2 ?_⟩
    refine hgV.boundary_le_boundary_of_lt_or_eq ?_ hy1
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · exact Or.inr ⟨by omega, by rw [Nat.bodd_succ]; cases j.bodd <;> rfl⟩
    · exact Or.inl (by omega)

theorem isRound_prod {U : LowerSet P} {V : LowerSet Q}
    (hrU : P.IsRound U) (hrV : Q.IsRound V) :
    (grayProduct P Q).IsRound (U ×ˢ V) := by
  have hgX := isGlobular_prod hrU.isGlobular hrV.isGlobular
  refine ⟨hgX, fun h0 => ?_, fun m hm => ?_⟩
  · refine eq_bot_iff.2 fun z ⟨h2, h1⟩ => ?_
    exact absurd (pos_and_mem_boundaryFull_prod hrU hrV (by simpa using h0) h1 h2).1
      (lt_irrefl 0)
  · refine le_antisymm (fun z ⟨h2, h1⟩ => (pos_and_mem_boundaryFull_prod hrU hrV hm h1 h2).2) ?_
    rw [boundaryFull]
    exact sup_le
      (le_inf (hgX.boundary_le_boundary (Nat.lt_succ_self m) false false)
        (hgX.boundary_le_boundary (Nat.lt_succ_self m) false true))
      (le_inf (hgX.boundary_le_boundary (Nat.lt_succ_self m) true false)
        (hgX.boundary_le_boundary (Nat.lt_succ_self m) true true))

theorem boundary_prod_eq_sup {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n j : ℕ} (hj : j < n) (α : Bool) :
    (grayProduct P Q).boundary (U ×ˢ V) n α =
      (grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α ⊔
        (grayProduct P Q).boundary
          (U ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) n α := by
  have hgA := hgU.boundary j α
  have hgB := hgV.boundary (n - j - 1) (xor (j + 1).bodd α)
  refine SetLike.ext fun ⟨x, y⟩ => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, hk, hx, hy⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    by_cases hkj : k ≤ j
    · refine Or.inl ((mem_boundary_prod_of_isGlobular hgA hgV).2 ⟨k, hk, ?_, hy⟩)
      rw [hgU.boundary_boundary_eq_of_le hkj (Or.inr rfl)]
      exact hx
    · refine Or.inr ((mem_boundary_prod_of_isGlobular hgU hgB).2 ⟨k, hk, hx, ?_⟩)
      rw [hgV.boundary_boundary_eq_of_le (show n - k ≤ n - j - 1 by omega) ?_]
      · exact hy
      · rcases eq_or_lt_of_le (show j + 1 ≤ k by omega) with rfl | h
        exacts [Or.inr rfl, Or.inl (by omega)]
  · refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ?_
    rcases h with h | h
    · obtain ⟨k, hk, hx, hy⟩ := (mem_boundary_prod_of_isGlobular hgA hgV).1 h
      exact ⟨k, hk, hgU.boundary_boundary_le (Or.inr rfl) hx, hy⟩
    · obtain ⟨k, hk, hx, hy⟩ := (mem_boundary_prod_of_isGlobular hgU hgB).1 h
      refine ⟨k, hk, hx, ?_⟩
      by_cases hlt : n - k < n - j - 1
      · rwa [hgV _ _ hlt] at hy
      · have hyB := boundary_le _ _ _ hy
        refine hgV.boundary_le_boundary_of_lt_or_eq ?_ hyB
        rcases eq_or_lt_of_le (show n - j - 1 ≤ n - k by omega) with h | h
        · refine Or.inr ⟨h, ?_⟩
          rw [show k = j + 1 by omega]
        · exact Or.inl h

theorem boundary_prod_inf {U : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) {n j : ℕ} (hj : j < n) (α : Bool) :
    (grayProduct P Q).boundary (P.boundary U j α ×ˢ V) n α ⊓
        (grayProduct P Q).boundary
          (U ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α)) n α =
      P.boundary U j α ×ˢ Q.boundary V (n - j - 1) (xor (j + 1).bodd α) := by
  have hgA := hgU.boundary j α
  have hgB := hgV.boundary (n - j - 1) (xor (j + 1).bodd α)
  refine SetLike.ext fun ⟨x, y⟩ => ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨hx, hy⟩ => ?_⟩
  · obtain ⟨k, _, hx, _⟩ := (mem_boundary_prod_of_isGlobular hgA hgV).1 h1
    obtain ⟨k', _, _, hy⟩ := (mem_boundary_prod_of_isGlobular hgU hgB).1 h2
    exact ⟨boundary_le _ k α hx, boundary_le _ _ _ hy⟩
  · refine ⟨(mem_boundary_prod_of_isGlobular hgA hgV).2 ⟨j, hj.le, ?_, ?_⟩,
      (mem_boundary_prod_of_isGlobular hgU hgB).2 ⟨j + 1, by omega, ?_, ?_⟩⟩
    · rw [hgU.boundary_boundary_eq_of_le le_rfl (Or.inr rfl)]
      exact hx
    · exact hgV.boundary_le_boundary (by omega) _ _ hy
    · exact hgU.boundary_le_boundary_of_le (Nat.le_succ j) α hx
    · rw [show n - (j + 1) = n - j - 1 by omega,
        boundary_eq_self (krullDim_boundary_le _ _ _)]
      exact hy

private theorem isMorphism_mk_left {x : P} (hx : IsMin x) :
    IsMorphism (P := Q) (Q := grayProduct P Q) (fun y : Q => (x, y)) where
  bijOn_faces y α := by
    have hx0 : grade ℕ x = 0 := grade_eq_zero_iff.2 hx
    refine ⟨fun y' hy' => mem_faces_grayProduct.2 (Or.inr ⟨rfl, by simpa [hx0] using hy'⟩),
      fun _ _ _ _ h => (Prod.mk.inj h).2, fun ⟨a, b⟩ hab => ?_⟩
    rcases mem_faces_grayProduct.1 hab with ⟨ha, rfl⟩ | ⟨rfl, hb⟩
    · exact (hx.not_lt ha.1.lt).elim
    · exact ⟨b, by simpa [hx0] using hb, rfl⟩

def grayProduct.inr {x : P} (hx : IsMin x) : Q ⟶ grayProduct P Q :=
  ConcreteCategory.ofHom ⟨fun y => (x, y), isMorphism_mk_left hx⟩

@[simp] theorem grayProduct.inr_apply {x : P} (hx : IsMin x) (y : Q) :
    grayProduct.inr hx y = (x, y) := rfl

instance grayProduct.instIsInclusionInr {x : P} (hx : IsMin x) :
    IsInclusion (grayProduct.inr (Q := Q) hx) :=
  ⟨fun _ _ h => (Prod.mk.inj h).2⟩

private theorem isMorphism_mk_right {y : Q} (hy : IsMin y) :
    IsMorphism (P := P) (Q := grayProduct P Q) (fun x : P => (x, y)) where
  bijOn_faces x α := by
    refine ⟨fun x' hx' => mem_faces_grayProduct.2 (Or.inl ⟨hx', rfl⟩),
      fun _ _ _ _ h => (Prod.mk.inj h).1, fun ⟨a, b⟩ hab => ?_⟩
    rcases mem_faces_grayProduct.1 hab with ⟨ha, rfl⟩ | ⟨rfl, hb⟩
    · exact ⟨a, ha, rfl⟩
    · exact (hy.not_lt hb.1.lt).elim

def grayProduct.inl {y : Q} (hy : IsMin y) : P ⟶ grayProduct P Q :=
  ConcreteCategory.ofHom ⟨fun x => (x, y), isMorphism_mk_right hy⟩

@[simp] theorem grayProduct.inl_apply {y : Q} (hy : IsMin y) (x : P) :
    grayProduct.inl hy x = (x, y) := rfl

instance grayProduct.instIsInclusionInl {y : Q} (hy : IsMin y) :
    IsInclusion (grayProduct.inl (P := P) hy) :=
  ⟨fun _ _ h => (Prod.mk.inj h).1⟩

theorem map_grayProduct_inr {x : P} (hx : IsMin x) (Z : LowerSet Q) :
    map (grayProduct.inr hx) Z = LowerSet.Iic x ×ˢ Z :=
  SetLike.ext fun ⟨_, b⟩ =>
    ⟨fun ⟨_, hy, h⟩ => ⟨(Prod.mk.inj h).1 ▸ le_rfl, (Prod.mk.inj h).2 ▸ hy⟩,
      fun ⟨ha, hb⟩ => ⟨b, hb, Prod.ext (hx.eq_of_le ha).symm rfl⟩⟩

theorem boundary_Iic_prod {x : P} (hx : IsMin x) (Z : LowerSet Q) (n : ℕ) (α : Bool) :
    (grayProduct P Q).boundary (LowerSet.Iic x ×ˢ Z) n α =
      LowerSet.Iic x ×ˢ Q.boundary Z n α := by
  rw [← map_grayProduct_inr hx, ← map_grayProduct_inr hx, map_boundary]

theorem isMoleculeIn_Iic_prod_iff {x : P} (hx : IsMin x) (Z : LowerSet Q) :
    IsMoleculeIn (grayProduct P Q) (LowerSet.Iic x ×ˢ Z) ↔ IsMoleculeIn Q Z := by
  rw [← map_grayProduct_inr hx, isMoleculeIn_map_iff]

theorem isSubmoleculeOf_Iic_prod_iff {x : P} (hx : IsMin x) {X Z : LowerSet Q} :
    (grayProduct P Q).IsSubmoleculeOf (LowerSet.Iic x ×ˢ X) (LowerSet.Iic x ×ˢ Z) ↔
      Q.IsSubmoleculeOf X Z := by
  rw [← map_grayProduct_inr hx, ← map_grayProduct_inr hx, isSubmoleculeOf_map_iff]

theorem boundary_prod_eq_self {X : LowerSet P} {Y : LowerSet Q} {i j n : ℕ}
    (hX : krullDim X ≤ i) (hY : krullDim Y ≤ j) (hn : i + j ≤ n) (α : Bool) :
    (grayProduct P Q).boundary (X ×ˢ Y) n α = X ×ˢ Y :=
  boundary_eq_self ((krullDim_prod_le hX hY).trans (by exact_mod_cast hn)) α

theorem boundary_prod_boundary_eq_self (U : LowerSet P) (V : LowerSet Q)
    {i j n : ℕ} (hn : i + j ≤ n) (α β γ : Bool) :
    (grayProduct P Q).boundary (P.boundary U i β ×ˢ Q.boundary V j γ) n α =
      P.boundary U i β ×ˢ Q.boundary V j γ :=
  boundary_prod_eq_self (krullDim_boundary_le U i β) (krullDim_boundary_le V j γ) hn α

theorem boundary_prod_congr {X U : LowerSet P} {Y V : LowerSet Q}
    (hgX : P.IsGlobular X) (hgU : P.IsGlobular U) (hgY : Q.IsGlobular Y) (hgV : Q.IsGlobular V)
    {n : ℕ} {α : Bool} (hXU : ∀ i ≤ n, P.boundary X i α = P.boundary U i α)
    (hYV : ∀ i ≤ n, Q.boundary Y (n - i) (xor i.bodd α) =
      Q.boundary V (n - i) (xor i.bodd α)) :
    (grayProduct P Q).boundary (X ×ˢ Y) n α = (grayProduct P Q).boundary (U ×ˢ V) n α :=
  SetLike.ext fun ⟨a, b⟩ => by
    rw [mem_boundary_prod_of_isGlobular hgX hgY, mem_boundary_prod_of_isGlobular hgU hgV]
    exact exists_congr fun i => and_congr_right fun hi => by rw [hXU i hi, hYV i hi]

theorem inf_boundary_prod_le {X U : LowerSet P} {Y V : LowerSet Q}
    (hgX : P.IsGlobular X) (hgU : P.IsGlobular U) (hgY : Q.IsGlobular Y) (hgV : Q.IsGlobular V)
    (hXU : ∀ i β, X ⊓ P.boundary U i β ≤ P.boundary X i β)
    (hYV : ∀ i β, Y ⊓ Q.boundary V i β ≤ Q.boundary Y i β) (n : ℕ) (α : Bool) :
    (X ×ˢ Y) ⊓ (grayProduct P Q).boundary (U ×ˢ V) n α ≤
      (grayProduct P Q).boundary (X ×ˢ Y) n α := by
  rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, h2⟩
  obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h2
  exact (mem_boundary_prod_of_isGlobular hgX hgY).2 ⟨i, hi,
    hXU i α ⟨ha, hai⟩, hYV _ _ ⟨hb, hbi⟩⟩

theorem inf_boundary_boundary_prod_le {X U : LowerSet P} {Y V : LowerSet Q}
    (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V) (hXU : P.IsSubmoleculeOf X U)
    (hYV : Q.IsSubmoleculeOf Y V) {m n : ℕ} (hmn : m < n) (α β : Bool) :
    (grayProduct P Q).boundary (X ×ˢ Y) n α ⊓ (grayProduct P Q).boundary (U ×ˢ V) m β ≤
      (grayProduct P Q).boundary ((grayProduct P Q).boundary (X ×ˢ Y) n α) m β := by
  have gX := hXU.isMoleculeIn.isGlobular
  have gY := hYV.isMoleculeIn.isGlobular
  rw [isGlobular_prod gX gY m n hmn β α]
  intro z ⟨hz1, hz2⟩
  exact inf_boundary_prod_le gX hU.isGlobular gY hV.isGlobular
    hXU.inf_boundary_le hYV.inf_boundary_le m β
    ⟨boundary_le (P := grayProduct P Q) (X ×ˢ Y) n α hz1, hz2⟩

theorem mem_boundary_prod_of_mem_left {W : LowerSet P} {V : LowerSet Q} {e m : ℕ} {α : Bool}
    (hgW : P.IsGlobular W) (hgV : Q.IsGlobular V) (hdV : krullDim V ≤ m) {a : P} {b : Q}
    (ha : a ∈ P.boundary W e α) (hb : b ∈ V) :
    ((a, b) : grayProduct P Q) ∈ (grayProduct P Q).boundary (W ×ˢ V) (e + m) α := by
  refine (mem_boundary_prod_of_isGlobular hgW hgV).2 ⟨e, by omega, ha, ?_⟩
  rwa [Nat.add_sub_cancel_left, boundary_eq_self hdV]

theorem mem_boundary_prod_of_mem_right {U : LowerSet P} {n e : ℕ} {α : Bool}
    (hgU : P.IsGlobular U) (hdU : krullDim U ≤ n) {W : LowerSet Q} (hgW : Q.IsGlobular W)
    {a : P} {b : Q} (ha : a ∈ U) (hb : b ∈ Q.boundary W e (!xor n.bodd α)) :
    ((a, b) : grayProduct P Q) ∈ (grayProduct P Q).boundary (U ×ˢ W) (e + n) (!α) := by
  refine (mem_boundary_prod_of_isGlobular hgU hgW).2 ⟨n, by omega, ?_, ?_⟩
  · rwa [boundary_eq_self hdU]
  · rwa [Nat.add_sub_cancel, Bool.xor_not]

theorem IsGlobular.boundary_add_sub_le {W : LowerSet Q} (hgW : Q.IsGlobular W) {n e i : ℕ}
    {α : Bool} (hni : n ≤ i) (hi : i ≤ e + n) :
    Q.boundary W (e + n - i) (xor i.bodd (!α)) ≤ Q.boundary W e (!xor n.bodd α) := by
  rcases hni.lt_or_eq with h | rfl
  · exact hgW.boundary_le_boundary (by omega) _ _
  · rw [Nat.add_sub_cancel, Bool.xor_not]

theorem prod_inf_boundary_prod_of_le_left {T U : LowerSet P} {V : LowerSet Q} {e m : ℕ}
    {α : Bool} (hgT : P.IsGlobular T) (hgU : P.IsGlobular U) (hdU : krullDim U ≤ e + 1)
    (hgV : Q.IsGlobular V) (hdV : krullDim V ≤ m) (hTU : T ≤ U)
    (hb : P.boundary T e (!α) = P.boundary U e (!α)) :
    T ×ˢ V ⊓ (grayProduct P Q).boundary (U ×ˢ V) (e + m) (!α) =
      (grayProduct P Q).boundary (T ×ˢ V) (e + m) (!α) := by
  have hdT : krullDim T ≤ e + 1 := (LowerSet.krullDim_mono hTU).trans hdU
  refine le_antisymm ?_ fun ⟨a, b⟩ h => ?_
  · rintro ⟨a, b⟩ ⟨⟨ha, hb'⟩, h⟩
    obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    by_cases hie : i ≤ e
    · refine mem_boundary_prod_of_mem_left hgT hgV hdV ?_ hb'
      rw [hb]
      exact hgU.boundary_le_boundary_of_le hie _ hai
    · refine (mem_boundary_prod_of_isGlobular hgT hgV).2 ⟨i, hi, ?_, hbi⟩
      rwa [boundary_eq_self (hdT.trans (by exact_mod_cast (by omega : e + 1 ≤ i)))]
  · obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgT hgV).1 h
    have hb' := boundary_le V _ _ hbi
    refine ⟨⟨boundary_le T i _ hai, hb'⟩, ?_⟩
    by_cases hie : i ≤ e
    · refine mem_boundary_prod_of_mem_left hgU hgV hdV ?_ hb'
      rw [← hb]
      exact hgT.boundary_le_boundary_of_le hie _ hai
    · refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, ?_, hbi⟩
      rw [boundary_eq_self (hdU.trans (by exact_mod_cast (by omega : e + 1 ≤ i)))]
      exact hTU (boundary_le T i _ hai)

theorem prod_inf_boundary_prod_of_le_right {U : LowerSet P} {n e : ℕ} {α : Bool}
    (hgU : P.IsGlobular U) (hdU : krullDim U ≤ n) {T V : LowerSet Q} (hgT : Q.IsGlobular T)
    (hgV : Q.IsGlobular V) (hdV : krullDim V ≤ e + 1) (hTV : T ≤ V)
    (hb : Q.boundary T e (!xor n.bodd α) = Q.boundary V e (!xor n.bodd α)) :
    U ×ˢ T ⊓ (grayProduct P Q).boundary (U ×ˢ V) (e + n) (!α) =
      (grayProduct P Q).boundary (U ×ˢ T) (e + n) (!α) := by
  have hdT : krullDim T ≤ e + 1 := (LowerSet.krullDim_mono hTV).trans hdV
  refine le_antisymm ?_ fun ⟨a, b⟩ h => ?_
  · rintro ⟨a, b⟩ ⟨⟨ha, hbT⟩, h⟩
    obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    by_cases hin : i < n
    · refine (mem_boundary_prod_of_isGlobular hgU hgT).2 ⟨i, hi, hai, ?_⟩
      rwa [boundary_eq_self (hdT.trans (by exact_mod_cast (by omega : e + 1 ≤ e + n - i)))]
    · refine mem_boundary_prod_of_mem_right hgU hdU hgT ha ?_
      rw [hb]
      exact hgV.boundary_add_sub_le (by omega) hi hbi
  · obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgU hgT).1 h
    have ha := boundary_le U i _ hai
    refine ⟨⟨ha, boundary_le T _ _ hbi⟩, ?_⟩
    by_cases hin : i < n
    · refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, hai, ?_⟩
      rw [boundary_eq_self (hdV.trans (by exact_mod_cast (by omega : e + 1 ≤ e + n - i)))]
      exact hTV (boundary_le T _ _ hbi)
    · refine mem_boundary_prod_of_mem_right hgU hdU hgV ha ?_
      rw [← hb]
      exact hgT.boundary_add_sub_le (by omega) hi hbi

theorem boundary_prod_eq_sup_of_split_left {U A B : LowerSet P} {V : LowerSet Q}
    (hgU : P.IsGlobular U) (hgA : P.IsGlobular A) (hgB : P.IsGlobular B) (hgV : Q.IsGlobular V)
    {k n : ℕ} (hkn : k < n) {α : Bool}
    (p1 : ∀ i ≤ k, P.boundary U i α = P.boundary A i α)
    (p2 : ∀ i, k < i → P.boundary U i α = P.boundary A i α ⊔ P.boundary B i α)
    (p3 : P.boundary B k α ≤ P.boundary A k (!α))
    (p4 : ∀ i < k, P.boundary B i α = P.boundary U i α) :
    (grayProduct P Q).boundary (U ×ˢ V) n α =
      (grayProduct P Q).boundary (A ×ˢ V) n α ⊔
        (grayProduct P Q).boundary
          (B ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) n α := by
  have hgY := hgV.boundary (n - k - 1) (xor k.bodd (!α))
  have hs : xor (k + 1).bodd α = xor k.bodd (!α) := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.xor_not]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    by_cases hik : i ≤ k
    · rw [p1 i hik] at ha
      exact Or.inl ((mem_boundary_prod_of_isGlobular hgA hgV).2 ⟨i, hi, ha, hb⟩)
    · rw [p2 i (by omega)] at ha
      rcases ha with ha | ha
      · exact Or.inl ((mem_boundary_prod_of_isGlobular hgA hgV).2 ⟨i, hi, ha, hb⟩)
      · refine Or.inr ((mem_boundary_prod_of_isGlobular hgB hgY).2 ⟨i, hi, ha, ?_⟩)
        rw [hgV.boundary_boundary_eq_of_le (show n - i ≤ n - k - 1 by omega) ?_]
        · exact hb
        · rcases eq_or_lt_of_le (show k + 1 ≤ i by omega) with rfl | h
          exacts [Or.inr hs, Or.inl (by omega)]
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgA hgV).1 h
    refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, ?_, hb⟩
    by_cases hik : i ≤ k
    · rw [p1 i hik]; exact ha
    · rw [p2 i (by omega)]; exact Or.inl ha
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgB hgY).1 h
    have hbY : b ∈ Q.boundary V (n - k - 1) (xor k.bodd (!α)) := boundary_le _ _ _ hb
    refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ?_
    rcases lt_trichotomy i k with hik | rfl | hik
    · refine ⟨i, hi, by rw [← p4 i hik]; exact ha, ?_⟩
      exact hgV.boundary_le_boundary (by omega) _ _ hbY
    · refine ⟨i + 1, by omega, ?_, ?_⟩
      · rw [p2 (i + 1) (Nat.lt_succ_self i)]
        exact Or.inl (hgA.boundary_le_boundary (Nat.lt_succ_self i) (!α) α (p3 ha))
      · rw [hs, show n - (i + 1) = n - i - 1 by omega]
        exact hbY
    · refine ⟨i, hi, by rw [p2 i hik]; exact Or.inr ha, ?_⟩
      refine hgV.boundary_boundary_le ?_ hb
      rcases eq_or_lt_of_le (show k + 1 ≤ i by omega) with rfl | h
      exacts [Or.inr hs, Or.inl (by omega)]

theorem boundary_prod_inf_of_split_left {A B : LowerSet P} {V : LowerSet Q}
    (hgA : P.IsGlobular A) (hgB : P.IsGlobular B) (hgV : Q.IsGlobular V) {k n : ℕ} (hkn : k < n)
    {α : Bool} (hAB : A ⊓ B = P.boundary A k (!α)) (hBA : A ⊓ B = P.boundary B k α) :
    (grayProduct P Q).boundary (A ×ˢ V) n α ⊓
        (grayProduct P Q).boundary
          (B ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) n α =
      P.boundary A k (!α) ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α)) := by
  have hgY := hgV.boundary (n - k - 1) (xor k.bodd (!α))
  have hs : xor (k + 1).bodd α = xor k.bodd (!α) := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.xor_not]
  refine le_antisymm ?_ ?_
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    have h1' := boundary_le (P := grayProduct P Q) (A ×ˢ V) n α h1
    have h2' := boundary_le (P := grayProduct P Q)
      (B ×ˢ Q.boundary V (n - k - 1) (xor k.bodd (!α))) n α h2
    have hab : a ∈ A ⊓ B := ⟨h1'.1, h2'.1⟩
    rw [hAB] at hab
    exact ⟨hab, h2'.2⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨(mem_boundary_prod_of_isGlobular hgA hgV).2
      ⟨k + 1, by omega, hgA.boundary_le_boundary (Nat.lt_succ_self k) (!α) α ha,
        by rw [hs, show n - (k + 1) = n - k - 1 by omega]; exact hb⟩,
      (mem_boundary_prod_of_isGlobular hgB hgY).2 ⟨k, hkn.le, ?_, ?_⟩⟩
    · rw [← hBA, hAB]; exact ha
    · rw [boundary_eq_self ((krullDim_boundary_le _ _ _).trans (by exact_mod_cast (by omega)))];
      exact hb

private theorem xor_bodd_add_sub {n i : ℕ} (hi : i ≤ n) (α : Bool) :
    xor (n + (n - i)).bodd α = xor i.bodd α := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left, show i + d + d = i + 2 * d by omega]
  simp [Nat.bodd_add]

theorem boundary_prod_eq_sup_of_split_right {U : LowerSet P} {V A B : LowerSet Q}
    (hgU : P.IsGlobular U) (hgV : Q.IsGlobular V) (hgA : Q.IsGlobular A) (hgB : Q.IsGlobular B)
    {k n : ℕ} (hkn : k < n) {α : Bool}
    (p1 : ∀ j ≤ k, Q.boundary V j (xor (n + j).bodd α) = Q.boundary A j (xor (n + j).bodd α))
    (p2 : ∀ j, k < j → Q.boundary V j (xor (n + j).bodd α) =
      Q.boundary A j (xor (n + j).bodd α) ⊔ Q.boundary B j (xor (n + j).bodd α))
    (p3 : Q.boundary B k (xor (n + k).bodd α) ≤ Q.boundary A k (!xor (n + k).bodd α))
    (p4 : ∀ j < k, Q.boundary B j (xor (n + j).bodd α) = Q.boundary V j (xor (n + j).bodd α)) :
    (grayProduct P Q).boundary (U ×ˢ V) n α =
      (grayProduct P Q).boundary (U ×ˢ A) n α ⊔
        (grayProduct P Q).boundary (P.boundary U (n - k - 1) α ×ˢ B) n α := by
  have hgY := hgU.boundary (n - k - 1) α
  have hp {i : ℕ} (hi : i ≤ n) := xor_bodd_add_sub hi α
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
    rw [← hp hi] at hb
    by_cases hik : n - i ≤ k
    · rw [p1 _ hik, hp hi] at hb
      exact Or.inl ((mem_boundary_prod_of_isGlobular hgU hgA).2 ⟨i, hi, ha, hb⟩)
    · rw [p2 _ (by omega), hp hi] at hb
      rcases hb with hb | hb
      · exact Or.inl ((mem_boundary_prod_of_isGlobular hgU hgA).2 ⟨i, hi, ha, hb⟩)
      · refine Or.inr ((mem_boundary_prod_of_isGlobular hgY hgB).2 ⟨i, hi, ?_, hb⟩)
        rwa [hgU.boundary_boundary_eq_of_le (show i ≤ n - k - 1 by omega) (Or.inr rfl)]
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgU hgA).1 h
    refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ⟨i, hi, ha, ?_⟩
    rw [← hp hi] at hb ⊢
    by_cases hik : n - i ≤ k
    · rw [p1 _ hik]; exact hb
    · rw [p2 _ (by omega)]; exact Or.inl hb
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, ha, hb⟩ := (mem_boundary_prod_of_isGlobular hgY hgB).1 h
    have haY : a ∈ P.boundary U (n - k - 1) α := boundary_le _ _ _ ha
    refine (mem_boundary_prod_of_isGlobular hgU hgV).2 ?_
    rw [← hp hi] at hb
    rcases lt_trichotomy (n - i) k with hik | hik | hik
    · refine ⟨i, hi, hgU.boundary_le_boundary (by omega) _ _ haY, ?_⟩
      rw [← hp hi, ← p4 _ hik]; exact hb
    · refine ⟨n - k - 1, by omega, haY, ?_⟩
      have hb' := p3 (by rw [← hik]; exact hb)
      rw [show n - (n - k - 1) = k + 1 by omega, ← hp (show n - k - 1 ≤ n by omega),
        show n - (n - k - 1) = k + 1 by omega, p2 _ (Nat.lt_succ_self k)]
      rw [show xor (n + (k + 1)).bodd α = !xor (n + k).bodd α by
        rw [← Nat.add_assoc, Nat.bodd_succ, Bool.not_xor]]
      exact Or.inl (hgA.boundary_le_boundary (Nat.lt_succ_self k) _ _ hb')
    · refine ⟨i, hi, ?_, ?_⟩
      · rwa [hgU.boundary_boundary_eq_of_le (show i ≤ n - k - 1 by omega) (Or.inr rfl)] at ha
      · rw [← hp hi, p2 _ hik]; exact Or.inr hb

theorem boundary_prod_inf_of_split_right {U : LowerSet P} {A B : LowerSet Q}
    (hgU : P.IsGlobular U) (hgA : Q.IsGlobular A) (hgB : Q.IsGlobular B) {k n : ℕ} (hkn : k < n)
    {α : Bool} (hAB : A ⊓ B = Q.boundary A k (!xor (n + k).bodd α))
    (hBA : A ⊓ B = Q.boundary B k (xor (n + k).bodd α)) :
    (grayProduct P Q).boundary (U ×ˢ A) n α ⊓
        (grayProduct P Q).boundary (P.boundary U (n - k - 1) α ×ˢ B) n α =
      P.boundary U (n - k - 1) α ×ˢ Q.boundary A k (!xor (n + k).bodd α) := by
  have hgY := hgU.boundary (n - k - 1) α
  refine le_antisymm ?_ ?_
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    have h1' := boundary_le (P := grayProduct P Q) (U ×ˢ A) n α h1
    have h2' := boundary_le (P := grayProduct P Q) (P.boundary U (n - k - 1) α ×ˢ B) n α h2
    have hab : b ∈ A ⊓ B := ⟨h1'.2, h2'.2⟩
    rw [hAB] at hab
    exact ⟨h2'.1, hab⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨(mem_boundary_prod_of_isGlobular hgU hgA).2 ⟨n - k - 1, by omega, ha, ?_⟩,
      (mem_boundary_prod_of_isGlobular hgY hgB).2 ⟨n - k, by omega, ?_, ?_⟩⟩
    · rw [show n - (n - k - 1) = k + 1 by omega, ← xor_bodd_add_sub (show n - k - 1 ≤ n by omega),
        show n - (n - k - 1) = k + 1 by omega, ← Nat.add_assoc, Nat.bodd_succ, Bool.not_xor]
      exact hgA.boundary_le_boundary (Nat.lt_succ_self k) _ _ hb
    · rw [boundary_eq_self ((krullDim_boundary_le _ _ _).trans (by exact_mod_cast (by omega)))]
      exact ha
    · rw [show n - (n - k) = k by omega, ← xor_bodd_add_sub (show n - k ≤ n by omega),
        show n - (n - k) = k by omega, ← hBA, hAB]
      exact hb

end Atoms.Molecule.OGP
