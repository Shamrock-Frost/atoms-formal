import Atoms.Molecule.Labelling.Map

universe w v u u₁

open Order CategoryTheory Bicategory

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} [Fintype P] [DecidableLE P] {B : Type u₁} [Bicategory.{w, v} B]
  {hP : P.IsRDC}

namespace Labelling

private theorem heq_compositeAlong (ℓ : Labelling B P hP) {M M' : LowerSet P}
    {_ : DecidablePred (· ∈ M)} {_ : DecidablePred (· ∈ M')} (e : M = M') (hM : IsMoleculeIn P M)
    (hM' : IsMoleculeIn P M') {xs ys : List P} (hxs : IsLayerOrder M xs)
    (hys : IsLayerOrder M' ys) {s t : P} (hs : P.boundary M 0 false = .Iic s)
    (ht : P.boundary M 0 true = .Iic t) (hs' : P.boundary M' 0 false = .Iic s)
    (ht' : P.boundary M' 0 true = .Iic t) :
    ℓ.compositeAlong hM hxs hs ht ≍ ℓ.compositeAlong hM' hys hs' ht' :=
  (ℓ.conjEqToHom_compositeAlong e hM hM' hxs hys hs ht hs' ht').heq

private theorem pathComp_pathOf_congr (ℓ : Labelling B P hP) {U V : LowerSet P}
    [DecidablePred (· ∈ U)] [DecidablePred (· ∈ V)] (e : U = V) {hU : IsMoleculeIn P U}
    {hd : krullDim U ≤ 1} {hV : IsMoleculeIn P V} {hdV : krullDim V ≤ 1} {v w : P}
    {hv : P.boundary U 0 false = .Iic v} {hw : P.boundary U 0 true = .Iic w}
    {hv' : P.boundary V 0 false = .Iic v} {hw' : P.boundary V 0 true = .Iic w} :
    pathComp ℓ.toPrefunctor (pathOf U hU hd hv hw) =
      pathComp ℓ.toPrefunctor (pathOf V hV hdV hv' hw') :=
  congrArg _ (pathOf_congr e)

omit [Fintype P] [DecidableLE P] in
private theorem boundary_one_boundary_two {M : LowerSet P} (hM : IsMoleculeIn P M) (α β : Bool) :
    P.boundary (P.boundary M 2 α) 1 β = P.boundary M 1 β :=
  hM.isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)

omit [Fintype P] [DecidableLE P] in
private theorem boundary_zero_boundary_two {M : LowerSet P} (hM : IsMoleculeIn P M) (α β : Bool) :
    P.boundary (P.boundary M 2 α) 0 β = P.boundary M 0 β :=
  hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)

private theorem heq_compositeAlong_paste_one (ℓ : Labelling B P hP)
    {V₁ V₂ W₁ W₂ U₁ U₂ : LowerSet P} [DecidablePred (· ∈ V₁)] [DecidablePred (· ∈ V₂)]
    [DecidablePred (· ∈ W₁)] [DecidablePred (· ∈ W₂)] [DecidablePred (· ∈ U₁)]
    [DecidablePred (· ∈ U₂)] (hV₁ : IsMoleculeIn P V₁) (hV₂ : IsMoleculeIn P V₂)
    (hW₁ : IsMoleculeIn P W₁) (hW₂ : IsMoleculeIn P W₂) (hU₁ : IsMoleculeIn P U₁)
    (hU₂ : IsMoleculeIn P U₂) (hp₁ : P.IsPastingIn 1 V₁ W₁ U₁) (hp₂ : P.IsPastingIn 1 V₂ W₂ U₂)
    (eV : ∀ β, P.boundary V₁ 1 β = P.boundary V₂ 1 β)
    (eW : ∀ β, P.boundary W₁ 1 β = P.boundary W₂ 1 β) {xs₁ xs₂ ys₁ ys₂ : List P}
    (hx₁ : IsLayerOrder V₁ xs₁) (hx₂ : IsLayerOrder W₁ xs₂) (hy₁ : IsLayerOrder V₂ ys₁)
    (hy₂ : IsLayerOrder W₂ ys₂) {s t : P} (hs : P.boundary U₁ 0 false = .Iic s)
    (ht : P.boundary U₁ 0 true = .Iic t) (hs' : P.boundary U₂ 0 false = .Iic s)
    (ht' : P.boundary U₂ 0 true = .Iic t)
    (hsV₁ : P.boundary V₁ 0 false = .Iic s) (htV₁ : P.boundary V₁ 0 true = .Iic t)
    (hsW₁ : P.boundary W₁ 0 false = .Iic s) (htW₁ : P.boundary W₁ 0 true = .Iic t)
    (hsV₂ : P.boundary V₂ 0 false = .Iic s) (htV₂ : P.boundary V₂ 0 true = .Iic t)
    (hsW₂ : P.boundary W₂ 0 false = .Iic s) (htW₂ : P.boundary W₂ 0 true = .Iic t)
    (hV : ℓ.compositeAlong hV₁ hx₁ hsV₁ htV₁ ≍ ℓ.compositeAlong hV₂ hy₁ hsV₂ htV₂)
    (hW : ℓ.compositeAlong hW₁ hx₂ hsW₁ htW₁ ≍ ℓ.compositeAlong hW₂ hy₂ hsW₂ htW₂) :
    ℓ.compositeAlong hU₁ (hx₁.append_of_isPastingIn_one hp₁ hx₂) hs ht ≍
      ℓ.compositeAlong hU₂ (hy₁.append_of_isPastingIn_one hp₂ hy₂) hs' ht' := by
  rw [ℓ.compositeAlong_append hU₁ hV₁ hW₁ hp₁ hx₁ hx₂ hs ht hsV₁ htV₁ hsW₁ htW₁,
    ℓ.compositeAlong_append hU₂ hV₂ hW₂ hp₂ hy₁ hy₂ hs' ht' hsV₂ htV₂ hsW₂ htW₂]
  refine (eqToHom_comp_heq _ _).trans ((heq_comp (pathComp_pathOf_congr ℓ (eV false))
    (pathComp_pathOf_congr ℓ (eV true)) (pathComp_pathOf_congr ℓ
      (hp₁.boundary_output.trans ((eW true).trans hp₂.boundary_output.symm))) hV ?_).trans
      (eqToHom_comp_heq _ _).symm)
  exact (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans (hW.trans
    ((comp_eqToHom_heq _ _).symm.trans (eqToHom_comp_heq _ _).symm)))

private theorem heq_horizontal {V : Type*} [Quiver V] (F : Prefunctor V B) {s m t : V}
    {p₁ p₂ r₁ r₂ : Quiver.Path s m} {q₁ q₂ u₁ u₂ : Quiver.Path m t} (hp : p₁ = p₂) (hq : q₁ = q₂)
    (hr : r₁ = r₂) (hu : u₁ = u₂) {X₁ X₂ Y₁ Y₂ : F.obj s ⟶ F.obj t} (hX : X₁ = X₂) (hY : Y₁ = Y₂)
    (e₁ : X₁ = pathComp F (p₁.comp q₁)) (e₂ : X₂ = pathComp F (p₂.comp q₂))
    (e₁' : pathComp F (r₁.comp u₁) = Y₁) (e₂' : pathComp F (r₂.comp u₂) = Y₂)
    {φ₁ : pathComp F p₁ ⟶ pathComp F r₁} {φ₂ : pathComp F p₂ ⟶ pathComp F r₂} (hφ : φ₁ ≍ φ₂)
    {ψ₁ : pathComp F q₁ ⟶ pathComp F u₁} {ψ₂ : pathComp F q₂ ⟶ pathComp F u₂} (hψ : ψ₁ ≍ ψ₂) :
    eqToHom e₁ ≫ (pathCompCompIso F p₁ q₁).hom ≫ (φ₁ ▷ pathComp F q₁ ≫ pathComp F r₁ ◁ ψ₁) ≫
        (pathCompCompIso F r₁ u₁).inv ≫ eqToHom e₁' ≍
      eqToHom e₂ ≫ (pathCompCompIso F p₂ q₂).hom ≫ (φ₂ ▷ pathComp F q₂ ≫ pathComp F r₂ ◁ ψ₂) ≫
        (pathCompCompIso F r₂ u₂).inv ≫ eqToHom e₂' := by
  subst hp hq hr hu hX hY
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hψ
  rfl

private theorem heq_compositeAlong_paste_zero (ℓ : Labelling B P hP)
    {V₁ V₂ W₁ W₂ U₁ U₂ : LowerSet P} [DecidablePred (· ∈ V₁)] [DecidablePred (· ∈ V₂)]
    [DecidablePred (· ∈ W₁)] [DecidablePred (· ∈ W₂)] [DecidablePred (· ∈ U₁)]
    [DecidablePred (· ∈ U₂)] (hV₁ : IsMoleculeIn P V₁) (hV₂ : IsMoleculeIn P V₂)
    (hW₁ : IsMoleculeIn P W₁) (hW₂ : IsMoleculeIn P W₂) (hU₁ : IsMoleculeIn P U₁)
    (hU₂ : IsMoleculeIn P U₂) (hp₁ : P.IsPastingIn 0 V₁ W₁ U₁) (hp₂ : P.IsPastingIn 0 V₂ W₂ U₂)
    (eV : ∀ β, P.boundary V₁ 1 β = P.boundary V₂ 1 β)
    (eW : ∀ β, P.boundary W₁ 1 β = P.boundary W₂ 1 β) {xs₁ xs₂ ys₁ ys₂ : List P}
    (hx₁ : IsLayerOrder V₁ xs₁) (hx₂ : IsLayerOrder W₁ xs₂) (hy₁ : IsLayerOrder V₂ ys₁)
    (hy₂ : IsLayerOrder W₂ ys₂) {s m t : P} (hs : P.boundary U₁ 0 false = .Iic s)
    (ht : P.boundary U₁ 0 true = .Iic t) (hs' : P.boundary U₂ 0 false = .Iic s)
    (ht' : P.boundary U₂ 0 true = .Iic t)
    (hsV₁ : P.boundary V₁ 0 false = .Iic s) (hmV₁ : P.boundary V₁ 0 true = .Iic m)
    (hmW₁ : P.boundary W₁ 0 false = .Iic m) (htW₁ : P.boundary W₁ 0 true = .Iic t)
    (hsV₂ : P.boundary V₂ 0 false = .Iic s) (hmV₂ : P.boundary V₂ 0 true = .Iic m)
    (hmW₂ : P.boundary W₂ 0 false = .Iic m) (htW₂ : P.boundary W₂ 0 true = .Iic t)
    (hV : ℓ.compositeAlong hV₁ hx₁ hsV₁ hmV₁ ≍ ℓ.compositeAlong hV₂ hy₁ hsV₂ hmV₂)
    (hW : ℓ.compositeAlong hW₁ hx₂ hmW₁ htW₁ ≍ ℓ.compositeAlong hW₂ hy₂ hmW₂ htW₂) :
    ℓ.compositeAlong hU₁ (hx₁.append_of_isPastingIn_zero hV₁ hW₁ hp₁ hx₂) hs ht ≍
      ℓ.compositeAlong hU₂ (hy₁.append_of_isPastingIn_zero hV₂ hW₂ hp₂ hy₂) hs' ht' := by
  have eU (β : Bool) : P.boundary U₁ 1 β = P.boundary U₂ 1 β :=
    (hp₁.boundary_of_lt hV₁.isGlobular hW₁.isGlobular zero_lt_one β).sup_eq.symm.trans
      ((congrArg₂ (· ⊔ ·) (eV β) (eW β)).trans
        (hp₂.boundary_of_lt hV₂.isGlobular hW₂.isGlobular zero_lt_one β).sup_eq)
  rw [ℓ.compositeAlong_append_of_isPastingIn_zero hU₁ hV₁ hW₁ hp₁ hx₁ hx₂ hs ht hsV₁ hmV₁ hmW₁
      htW₁,
    ℓ.compositeAlong_append_of_isPastingIn_zero hU₂ hV₂ hW₂ hp₂ hy₁ hy₂ hs' ht' hsV₂ hmV₂ hmW₂
      htW₂]
  exact heq_horizontal ℓ.toPrefunctor (pathOf_congr (eV false)) (pathOf_congr (eW false))
    (pathOf_congr (eV true)) (pathOf_congr (eW true)) (pathComp_pathOf_congr ℓ (eU false))
    (pathComp_pathOf_congr ℓ (eU true)) _ _ _ _ hV hW

private theorem heq_compositeAlong_boundary_of_krullDim_le (ℓ : Labelling B P hP)
    {M : LowerSet P} [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) (hd : krullDim M ≤ 2)
    {s t : P} (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t)
    {xs ys : List P} (hxs : IsLayerOrder (P.boundary M 2 false) xs)
    (hys : IsLayerOrder (P.boundary M 2 true) ys) :
    ℓ.compositeAlong (hM.boundary 2 false) hxs
        ((boundary_zero_boundary_two hM false false).trans hs)
        ((boundary_zero_boundary_two hM false true).trans ht) ≍
      ℓ.compositeAlong (hM.boundary 2 true) hys
        ((boundary_zero_boundary_two hM true false).trans hs)
        ((boundary_zero_boundary_two hM true true).trans ht) :=
  heq_compositeAlong ℓ ((boundary_eq_self hd false).trans (boundary_eq_self hd true).symm) _ _ _ _
    _ _ _ _

private theorem IsCommutative.heq_compositeAlong_boundary {ℓ : Labelling B P hP}
    (hℓ : ℓ.IsCommutative) {M : LowerSet P} (hM : IsMoleculeIn P M) :
    ∀ [DecidablePred (· ∈ M)] {s t : P} (hs : P.boundary M 0 false = .Iic s)
      (ht : P.boundary M 0 true = .Iic t) {xs ys : List P}
      (hxs : IsLayerOrder (P.boundary M 2 false) xs)
      (hys : IsLayerOrder (P.boundary M 2 true) ys),
      ℓ.compositeAlong (hM.boundary 2 false) hxs
          ((boundary_zero_boundary_two hM false false).trans hs)
          ((boundary_zero_boundary_two hM false true).trans ht) ≍
        ℓ.compositeAlong (hM.boundary 2 true) hys
          ((boundary_zero_boundary_two hM true false).trans hs)
          ((boundary_zero_boundary_two hM true true).trans ht) := by
  classical
  induction hM with
  | point x hx =>
    intro _ s t hs ht xs ys hxs hys
    have h0 : grade ℕ x = 0 := (hx.grade ℕ).eq_bot
    refine heq_compositeAlong_boundary_of_krullDim_le ℓ (.point x hx) ?_ hs ht hxs hys
    rw [LowerSet.krullDim_Iic, h0]
    exact_mod_cast Nat.zero_le 2
  | atom y hround hbdry ih =>
    intro _ s t hs ht xs ys hxs hys
    have hM : IsMoleculeIn P (.Iic y) := .atom y hround hbdry
    by_cases hd : krullDim (LowerSet.Iic y) ≤ 2
    · exact heq_compositeAlong_boundary_of_krullDim_le ℓ hM hd hs ht hxs hys
    have hy : 3 ≤ grade ℕ y := by
      rw [LowerSet.krullDim_Iic] at hd
      by_contra h
      exact hd (by exact_mod_cast (show grade ℕ y ≤ 2 by omega))
    rcases hy.lt_or_eq with hy | hy
    · obtain ⟨n, hn⟩ : ∃ n, grade ℕ y = n + 1 := ⟨grade ℕ y - 1, by omega⟩
      have hk : krullDim (LowerSet.Iic y) = (n + 1 : ℕ) := by rw [LowerSet.krullDim_Iic, hn]
      have hN := hbdry false
      have e (α : Bool) : P.boundary (P.bdry (.Iic y) false) 2 α = P.boundary (.Iic y) 2 α := by
        rw [bdry_eq_boundary hk]
        exact hround.isGlobular.boundary_boundary_eq_of_le (by omega) (.inl (by omega))
      have e₀ (α : Bool) : P.boundary (P.bdry (.Iic y) false) 0 α = P.boundary (.Iic y) 0 α := by
        rw [bdry_eq_boundary hk]
        exact hround.isGlobular.boundary_boundary_eq_of_le (by omega) (.inl (by omega))
      obtain ⟨xs₀, hxs₀⟩ := exists_isLayerOrder_of_krullDim_le (hN.boundary 2 false)
        ((krullDim_boundary_le _ 2 false).trans_eq Nat.cast_ofNat)
      obtain ⟨ys₀, hys₀⟩ := exists_isLayerOrder_of_krullDim_le (hN.boundary 2 true)
        ((krullDim_boundary_le _ 2 true).trans_eq Nat.cast_ofNat)
      exact (heq_compositeAlong ℓ (e false).symm _ _ _ _ _ _ _ _).trans
        ((ih false ((e₀ false).trans hs) ((e₀ true).trans ht) hxs₀ hys₀).trans
          (heq_compositeAlong ℓ (e true) _ _ _ _ _ _ _ _))
    · have h := hℓ y hy.symm hs ht hxs hys
      have h' := (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans
        ((heq_of_eq h).trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))
      exact (heq_compositeAlong ℓ rfl _ _ _ _ _ _ _ _).trans
        (h'.trans (heq_compositeAlong ℓ rfl _ _ _ _ _ _ _ _))
  | paste k V W U hp hV hW hk ihV ihW =>
    intro _ s t hs ht xs ys hxs hys
    have hU : IsMoleculeIn P U := .paste k V W U hp hV hW hk
    by_cases hd : krullDim U ≤ 2
    · exact heq_compositeAlong_boundary_of_krullDim_le ℓ hU hd hs ht hxs hys
    have hlo {N : LowerSet P} (hN : IsMoleculeIn P N) (α : Bool) :
        ∃ zs, IsLayerOrder (P.boundary N 2 α) zs :=
      exists_isLayerOrder_of_krullDim_le (hN.boundary 2 α)
        ((krullDim_boundary_le _ 2 α).trans_eq Nat.cast_ofNat)
    obtain ⟨a₁, ha₁⟩ := hlo hV false
    obtain ⟨a₂, ha₂⟩ := hlo hV true
    obtain ⟨b₁, hb₁⟩ := hlo hW false
    obtain ⟨b₂, hb₂⟩ := hlo hW true
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hpα (α : Bool) := hp.boundary_of_lt hV.isGlobular hW.isGlobular hk2 α
      have eV (β : Bool) : P.boundary (P.boundary V 2 false) 1 β =
          P.boundary (P.boundary V 2 true) 1 β :=
        (boundary_one_boundary_two hV false β).trans (boundary_one_boundary_two hV true β).symm
      have eW (β : Bool) : P.boundary (P.boundary W 2 false) 1 β =
          P.boundary (P.boundary W 2 true) 1 β :=
        (boundary_one_boundary_two hW false β).trans (boundary_one_boundary_two hW true β).symm
      rcases Nat.lt_or_ge k 1 with hk1 | hk1
      · obtain rfl : k = 0 := by omega
        have hm : P.boundary V 0 true = P.boundary W 0 false :=
          hp.inf_eq_output.symm.trans hp.inf_eq_input
        have hsV := hp.boundary_input.symm.trans hs
        have htW := hp.boundary_output.symm.trans ht
        have hmV := boundary_zero_eq_Iic_vertex V hV true
        have hmW := hm.symm.trans hmV
        have h₁ := ha₁.append_of_isPastingIn_zero (hV.boundary 2 false) (hW.boundary 2 false)
          (hpα false) hb₁
        have h₂ := ha₂.append_of_isPastingIn_zero (hV.boundary 2 true) (hW.boundary 2 true)
          (hpα true) hb₂
        refine (heq_of_eq (ℓ.compositeAlong_eq _ _ _ hxs h₁)).trans (HEq.trans ?_
          (heq_of_eq (ℓ.compositeAlong_eq _ _ _ h₂ hys)))
        exact heq_compositeAlong_paste_zero ℓ (hV.boundary 2 false) (hV.boundary 2 true)
          (hW.boundary 2 false) (hW.boundary 2 true) (hU.boundary 2 false) (hU.boundary 2 true)
          (hpα false) (hpα true) eV eW ha₁ hb₁ ha₂ hb₂ _ _ _ _
          ((boundary_zero_boundary_two hV false false).trans hsV)
          ((boundary_zero_boundary_two hV false true).trans hmV)
          ((boundary_zero_boundary_two hW false false).trans hmW)
          ((boundary_zero_boundary_two hW false true).trans htW)
          ((boundary_zero_boundary_two hV true false).trans hsV)
          ((boundary_zero_boundary_two hV true true).trans hmV)
          ((boundary_zero_boundary_two hW true false).trans hmW)
          ((boundary_zero_boundary_two hW true true).trans htW)
          (ihV hsV hmV ha₁ ha₂) (ihW hmW htW hb₁ hb₂)
      · obtain rfl : k = 1 := by omega
        have hsV := (hp.boundary_eq_of_lt_cond (A := W) (B := V) false hW.isGlobular
          hV.isGlobular zero_lt_one false).symm.trans hs
        have htV := (hp.boundary_eq_of_lt_cond (A := W) (B := V) false hW.isGlobular
          hV.isGlobular zero_lt_one true).symm.trans ht
        have hsW := (hp.boundary_eq_of_lt_cond (A := V) (B := W) true hV.isGlobular
          hW.isGlobular zero_lt_one false).symm.trans hs
        have htW := (hp.boundary_eq_of_lt_cond (A := V) (B := W) true hV.isGlobular
          hW.isGlobular zero_lt_one true).symm.trans ht
        have h₁ := ha₁.append_of_isPastingIn_one (hpα false) hb₁
        have h₂ := ha₂.append_of_isPastingIn_one (hpα true) hb₂
        refine (heq_of_eq (ℓ.compositeAlong_eq _ _ _ hxs h₁)).trans (HEq.trans ?_
          (heq_of_eq (ℓ.compositeAlong_eq _ _ _ h₂ hys)))
        exact heq_compositeAlong_paste_one ℓ (hV.boundary 2 false) (hV.boundary 2 true)
          (hW.boundary 2 false) (hW.boundary 2 true) (hU.boundary 2 false) (hU.boundary 2 true)
          (hpα false) (hpα true) eV eW ha₁ hb₁ ha₂ hb₂ _ _ _ _
          ((boundary_zero_boundary_two hV false false).trans hsV)
          ((boundary_zero_boundary_two hV false true).trans htV)
          ((boundary_zero_boundary_two hW false false).trans hsW)
          ((boundary_zero_boundary_two hW false true).trans htW)
          ((boundary_zero_boundary_two hV true false).trans hsV)
          ((boundary_zero_boundary_two hV true true).trans htV)
          ((boundary_zero_boundary_two hW true false).trans hsW)
          ((boundary_zero_boundary_two hW true true).trans htW)
          (ihV hsV htV ha₁ ha₂) (ihW hsW htW hb₁ hb₂)
    · have hsV := (hp.boundary_eq_of_lt_cond (A := W) (B := V) false hW.isGlobular
        hV.isGlobular (by omega : 0 < k) false).symm.trans hs
      have htV := (hp.boundary_eq_of_lt_cond (A := W) (B := V) false hW.isGlobular
        hV.isGlobular (by omega : 0 < k) true).symm.trans ht
      rcases hk2.lt_or_eq with hk3 | rfl
      · have e (α : Bool) : P.boundary U 2 α = P.boundary V 2 α :=
          hp.boundary_eq_of_lt_cond (A := W) (B := V) false hW.isGlobular hV.isGlobular hk3 α
        exact (heq_compositeAlong ℓ (e false) _ _ _ _ _ _ _ _).trans ((ihV hsV htV ha₁ ha₂).trans
          (heq_compositeAlong ℓ (e true).symm _ _ _ _ _ _ _ _))
      · have hsW := (hp.boundary_eq_of_lt_cond (A := V) (B := W) true hV.isGlobular
          hW.isGlobular two_pos false).symm.trans hs
        have htW := (hp.boundary_eq_of_lt_cond (A := V) (B := W) true hV.isGlobular
          hW.isGlobular two_pos true).symm.trans ht
        exact (heq_compositeAlong ℓ hp.boundary_input _ _ _ _ _ _ _ _).trans
          ((ihV hsV htV ha₁ ha₂).trans ((heq_compositeAlong ℓ
            (hp.inf_eq_output.symm.trans hp.inf_eq_input) _ _ _ _ _ _ _ _).trans
              ((ihW hsW htW hb₁ hb₂).trans
                (heq_compositeAlong ℓ hp.boundary_output.symm _ _ _ _ _ _ _ _))))

theorem IsCommutative.compositeAlong_boundary_eq {ℓ : Labelling B P hP} (hℓ : ℓ.IsCommutative)
    {M : LowerSet P} [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {s t : P}
    (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {xs ys : List P}
    (hxs : IsLayerOrder (P.boundary M 2 false) xs)
    (hys : IsLayerOrder (P.boundary M 2 true) ys) :
    eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hU := hM.boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (hw := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
        (hM.isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      ℓ.compositeAlong (hM.boundary 2 false) hxs
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hV := hM.boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (hw' := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
        (hM.isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)))) =
    eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hU := hM.boundary 1 false)
        (hd := (krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (hv := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (hw := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
        (hM.isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)).symm)) ≫
      ℓ.compositeAlong (hM.boundary 2 true) hys
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) ≫
      eqToHom (congrArg (pathComp ℓ.toPrefunctor) (pathOf_congr (hV := hM.boundary 1 true)
        (hdV := (krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (hv' := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (hw' := (hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)
        (hM.isGlobular.boundary_boundary_eq_of_le one_le_two (.inl one_lt_two)))) :=
  eq_of_heq (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
    ((hℓ.heq_compositeAlong_boundary hM hs ht hxs hys).trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm))

theorem IsCommutative.pathCell_boundary_eq {ℓ : Labelling B P hP} (hℓ : ℓ.IsCommutative)
    {M : LowerSet P} [DecidablePred (· ∈ M)] (hM : IsMoleculeIn P M) {s t : P}
    (hs : P.boundary M 0 false = .Iic s) (ht : P.boundary M 0 true = .Iic t) {xs ys : List P}
    (hxs : IsLayerOrder (P.boundary M 2 false) xs)
    (hys : IsLayerOrder (P.boundary M 2 true) ys) :
    ℓ.pathCell (hM.boundary 2 false) hxs
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) =
      ℓ.pathCell (hM.boundary 2 true) hys
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) :=
  PathCell.ext rfl rfl
    (heq_of_eq (congrArg _ (pathOf_congr ((boundary_one_boundary_two hM false false).trans
      (boundary_one_boundary_two hM true false).symm))))
    (heq_of_eq (congrArg _ (pathOf_congr ((boundary_one_boundary_two hM false true).trans
      (boundary_one_boundary_two hM true true).symm))))
    (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
      ((hℓ.heq_compositeAlong_boundary hM hs ht hxs hys).trans
        ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm))

end Labelling

section Extension

variable (M : LowerSet P)

abbrev inclMap : Map (P.restrict M) P := ⟨incl M, isMap_of_isInclusion _⟩

omit [Fintype P] [DecidableLE P] in
theorem boundary_restrict_Iic {x v : P.restrict M} {n : ℕ} {α : Bool}
    (h : P.boundary (.Iic x.1) n α = .Iic v.1) :
    (P.restrict M).boundary (.Iic x) n α = .Iic v := by
  refine map_injective (incl M) ?_
  rw [map_boundary, map_Iic, map_Iic]
  exact h

omit [Fintype P] [DecidableLE P] in
theorem mem_of_boundary_Iic {x v : P} (hx : x ∈ M) {n : ℕ} {α : Bool}
    (h : P.boundary (.Iic x) n α = .Iic v) : v ∈ M := by
  have hv : v ∈ P.boundary (.Iic x) n α := by
    rw [h]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  exact M.lower (LowerSet.mem_Iic_iff.1 (boundary_le _ n α hv)) hx

private theorem comp_heq_comp {a b c a' b' c' : B} (ha : a = a') (hb : b = b') (hc : c = c')
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'} (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  subst ha hb hc
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

omit [Fintype P] [DecidableLE P] in
private theorem heq_path_nil {V : Type*} [Quiver V] {a a' : V} (h : a = a') :
    (Quiver.Path.nil : Quiver.Path a a) ≍ (Quiver.Path.nil : Quiver.Path a' a') := by
  subst h
  rfl

omit [Fintype P] [DecidableLE P] in
private theorem heq_path_cons {V : Type*} [Quiver V] {a b c a' b' c' : V} (ha : a = a')
    (hb : b = b') (hc : c = c') {p : Quiver.Path a b} {p' : Quiver.Path a' b'} {e : b ⟶ c}
    {e' : b' ⟶ c'} (hp : p ≍ p') (he : e ≍ e') : p.cons e ≍ p'.cons e' := by
  subst ha hb hc
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq he
  rfl

variable [DecidablePred (· ∈ M)] [Fintype (P.restrict M)] [DecidableLE (P.restrict M)]
  {hM : (P.restrict M).IsRDC}

namespace Labelling

variable {M} (ℓ : Labelling B (P.restrict M) hM) (b₀ : B)

def extendObj (y : P) : B :=
  if h : vertex (.Iic y) (hP y) false ∈ M then ℓ.toPrefunctor.obj ⟨_, h⟩ else b₀

private theorem extendObj_eq_of_boundary_Iic {y v : P} (hv : P.boundary (.Iic y) 0 false = .Iic v) :
    ℓ.extendObj (hP := hP) b₀ y = if h : v ∈ M then ℓ.toPrefunctor.obj ⟨v, h⟩ else b₀ := by
  obtain rfl := vertex_eq_of_boundary_zero_eq_Iic _ (hP y) hv
  rfl

theorem extendObj_of_mem {y : P} (h : y ∈ M) :
    ℓ.extendObj (hP := hP) b₀ y = ℓ.toPrefunctor.obj ⟨y, h⟩ := by
  have hv := boundary_zero_eq_Iic_vertex _ (hP y) false
  exact (dif_pos (mem_of_boundary_Iic M h hv)).trans (ℓ.obj_eq_of_boundary_Iic ⟨y, h⟩
    (boundary_restrict_Iic M (v := ⟨_, mem_of_boundary_Iic M h hv⟩) hv)).symm

def restrictEdge {v w : EdgeQuiver P} (e : v ⟶ w) (he : e.1 ∈ M) :
    Quiver.Hom (V := EdgeQuiver (P.restrict M))
      (⟨v, mem_of_boundary_Iic M he e.2.2.1⟩ : P.restrict M)
      (⟨w, mem_of_boundary_Iic M he e.2.2.2⟩ : P.restrict M) :=
  ⟨⟨e.1, he⟩, ((isMorphism (incl M)).grade_eq ⟨e.1, he⟩).trans e.2.1,
    boundary_restrict_Iic M e.2.2.1, boundary_restrict_Iic M e.2.2.2⟩

def extendPrefunctor
    (edge : ∀ {v w : EdgeQuiver P} (e : v ⟶ w), e.1 ∉ M →
      (ℓ.extendObj (hP := hP) b₀ v ⟶ ℓ.extendObj (hP := hP) b₀ w)) :
    Prefunctor (EdgeQuiver P) B where
  obj := ℓ.extendObj b₀
  map e := if he : e.1 ∈ M then
      Quiver.homOfEq (ℓ.toPrefunctor.map (restrictEdge e he))
        (ℓ.extendObj_of_mem b₀ _).symm (ℓ.extendObj_of_mem b₀ _).symm
    else edge e he

variable (edge : ∀ {v w : EdgeQuiver P} (e : v ⟶ w), e.1 ∉ M →
  (ℓ.extendObj (hP := hP) b₀ v ⟶ ℓ.extendObj (hP := hP) b₀ w))

theorem extendPrefunctor_map_of_mem {v w : EdgeQuiver P} (e : v ⟶ w) (he : e.1 ∈ M) :
    (ℓ.extendPrefunctor b₀ @edge).map e = Quiver.homOfEq (ℓ.toPrefunctor.map (restrictEdge e he))
      (ℓ.extendObj_of_mem b₀ _).symm (ℓ.extendObj_of_mem b₀ _).symm :=
  dif_pos he

theorem extendPrefunctor_map_of_not_mem {v w : EdgeQuiver P} (e : v ⟶ w) (he : e.1 ∉ M) :
    (ℓ.extendPrefunctor b₀ @edge).map e = edge e he :=
  dif_neg he

theorem pathComp_extendPrefunctor_mapPath {a : EdgeQuiver (P.restrict M)} :
    ∀ {b : EdgeQuiver (P.restrict M)} (p : Quiver.Path a b),
      pathComp (ℓ.extendPrefunctor b₀ @edge) ((inclMap M).mapPath p) ≍ pathComp ℓ.toPrefunctor p
  | _, .nil => by
    have h : (ℓ.extendPrefunctor b₀ @edge).obj ((inclMap M) a) = ℓ.toPrefunctor.obj a :=
      ℓ.extendObj_of_mem b₀ a.2
    rw [Map.mapPath, pathComp_nil, pathComp_nil, h]
  | _, .cons (b := c) p e => by
    have hg : grade ℕ ((inclMap M) e.1) = 1 := ((isMorphism (incl M)).grade_eq e.1).trans e.2.1
    rw [Map.mapPath, dif_pos hg, pathComp_cons, pathComp_cons]
    refine comp_heq_comp (ℓ.extendObj_of_mem b₀ a.2) (ℓ.extendObj_of_mem b₀ c.2)
      (ℓ.extendObj_of_mem b₀ _) (pathComp_extendPrefunctor_mapPath p) ?_
    rw [extendPrefunctor_map_of_mem _ _ _ _ e.1.2]
    exact Quiver.homOfEq_heq _ _ _

theorem mapPath_extendPrefunctor_mapPath {a : EdgeQuiver (P.restrict M)} :
    ∀ {b : EdgeQuiver (P.restrict M)} (p : Quiver.Path a b),
      (ℓ.extendPrefunctor b₀ @edge).mapPath ((inclMap M).mapPath p) ≍ ℓ.toPrefunctor.mapPath p
  | _, .nil => by
    rw [Map.mapPath, Prefunctor.mapPath_nil, Prefunctor.mapPath_nil]
    exact heq_path_nil (ℓ.extendObj_of_mem b₀ a.2)
  | _, .cons (b := c) p e => by
    have hg : grade ℕ ((inclMap M) e.1) = 1 := ((isMorphism (incl M)).grade_eq e.1).trans e.2.1
    rw [Map.mapPath, dif_pos hg, Prefunctor.mapPath_cons, Prefunctor.mapPath_cons]
    refine heq_path_cons (ℓ.extendObj_of_mem b₀ a.2) (ℓ.extendObj_of_mem b₀ c.2)
      (ℓ.extendObj_of_mem b₀ _) (mapPath_extendPrefunctor_mapPath p) ?_
    rw [extendPrefunctor_map_of_mem _ _ _ _ e.1.2]
    exact Quiver.homOfEq_heq _ _ _

def castHom {a b a' b' : B} {f g : a ⟶ b} {f' g' : a' ⟶ b'} (ha : a = a') (hb : b = b')
    (hf : f ≍ f') (hg : g ≍ g') (φ : f ⟶ g) : f' ⟶ g' := by
  subst ha hb
  exact eqToHom (eq_of_heq hf).symm ≫ φ ≫ eqToHom (eq_of_heq hg)

theorem castHom_heq {a b a' b' : B} {f g : a ⟶ b} {f' g' : a' ⟶ b'} (ha : a = a') (hb : b = b')
    (hf : f ≍ f') (hg : g ≍ g') (φ : f ⟶ g) : castHom ha hb hf hg φ ≍ φ := by
  subst ha hb
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  simp only [castHom, eqToHom_refl, Category.id_comp, Category.comp_id, heq_eq_eq]

theorem pathComp_extendPrefunctor_pathOf {x : P} (hx : x ∈ M) (α : Bool) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    pathComp (ℓ.extendPrefunctor b₀ @edge) (pathOf (P.boundary (.Iic x) 1 α) ((hP x).boundary 1 α)
        ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) ≍
      pathComp ℓ.toPrefunctor (pathOf ((P.restrict M).boundary (.Iic ⟨x, hx⟩) 1 α)
        ((hM ⟨x, hx⟩).boundary 1 α) ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          (boundary_restrict_Iic M (v := ⟨s, mem_of_boundary_Iic M hx hs⟩) hs))
        (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          (boundary_restrict_Iic M (v := ⟨t, mem_of_boundary_Iic M hx ht⟩) ht))) := by
  have e : @Eq (Quiver.Path (V := EdgeQuiver P) s t)
      (pathOf (P.boundary (.Iic x) 1 α) ((hP x).boundary 1 α)
        ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht))
      ((inclMap M).mapPath (pathOf ((P.restrict M).boundary (.Iic ⟨x, hx⟩) 1 α)
        ((hM ⟨x, hx⟩).boundary 1 α) ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          (boundary_restrict_Iic M (v := ⟨s, mem_of_boundary_Iic M hx hs⟩) hs))
        (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
          (boundary_restrict_Iic M (v := ⟨t, mem_of_boundary_Iic M hx ht⟩) ht)))) :=
    ((inclMap M).mapPath_pathOf_boundary hM hP ⟨x, hx⟩ α
      (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        (boundary_restrict_Iic M (v := ⟨s, mem_of_boundary_Iic M hx hs⟩) hs))
      (((hM ⟨x, hx⟩).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans
        (boundary_restrict_Iic M (v := ⟨t, mem_of_boundary_Iic M hx ht⟩) ht))).symm
  rw [e]
  exact ℓ.pathComp_extendPrefunctor_mapPath b₀ @edge _

variable (cell : ∀ (x : P), grade ℕ x = 2 → ∀ {s t : P}
  (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t), x ∉ M →
    (pathComp (ℓ.extendPrefunctor b₀ @edge) (pathOf (P.boundary (.Iic x) 1 false)
        ((hP x).boundary 1 false) ((krullDim_boundary_le _ 1 false).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) ⟶
      pathComp (ℓ.extendPrefunctor b₀ @edge) (pathOf (P.boundary (.Iic x) 1 true)
        ((hP x).boundary 1 true) ((krullDim_boundary_le _ 1 true).trans_eq Nat.cast_one)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        (((hP x).isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht))))

def extend : Labelling B P hP where
  toPrefunctor := ℓ.extendPrefunctor b₀ @edge
  obj_eq_of_boundary_Iic _ _ hv := (ℓ.extendObj_eq_of_boundary_Iic b₀ hv).trans
    (ℓ.extendObj_eq_of_boundary_Iic b₀ (boundary_Iic_of_isMin
      (grade_eq_zero_iff.1 (grade_eq_zero_of_boundary_zero_eq_Iic hv)) 0 false)).symm
  cell x hx s t hs ht := if hxM : x ∈ M then
      castHom (ℓ.extendObj_of_mem b₀ (mem_of_boundary_Iic M hxM hs)).symm
        (ℓ.extendObj_of_mem b₀ (mem_of_boundary_Iic M hxM ht)).symm
        (ℓ.pathComp_extendPrefunctor_pathOf b₀ @edge (hP := hP) hxM false hs ht).symm
        (ℓ.pathComp_extendPrefunctor_pathOf b₀ @edge (hP := hP) hxM true hs ht).symm
        (ℓ.cell ⟨x, hxM⟩ (((isMorphism (incl M)).grade_eq ⟨x, hxM⟩).trans hx)
          (boundary_restrict_Iic M (v := ⟨s, mem_of_boundary_Iic M hxM hs⟩) hs)
          (boundary_restrict_Iic M (v := ⟨t, mem_of_boundary_Iic M hxM ht⟩) ht))
    else cell x hx hs ht hxM

theorem extend_cell_heq_of_mem {x : P} (hxM : x ∈ M) (hx : grade ℕ x = 2) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    (ℓ.extend b₀ @edge cell (hP := hP)).cell x hx hs ht ≍
      ℓ.cell ⟨x, hxM⟩ (((isMorphism (incl M)).grade_eq ⟨x, hxM⟩).trans hx)
        (boundary_restrict_Iic M (v := ⟨s, mem_of_boundary_Iic M hxM hs⟩) hs)
        (boundary_restrict_Iic M (v := ⟨t, mem_of_boundary_Iic M hxM ht⟩) ht) :=
  (heq_of_eq (dif_pos hxM)).trans (castHom_heq _ _ _ _ _)

theorem extend_cell_of_not_mem {x : P} (hxM : x ∉ M) (hx : grade ℕ x = 2) {s t : P}
    (hs : P.boundary (.Iic x) 0 false = .Iic s) (ht : P.boundary (.Iic x) 0 true = .Iic t) :
    (ℓ.extend b₀ @edge cell (hP := hP)).cell x hx hs ht = cell x hx hs ht hxM :=
  dif_neg hxM

theorem comap_extend : (ℓ.extend b₀ @edge cell (hP := hP)).comap (inclMap M) hM = ℓ := by
  refine Labelling.ext (Prefunctor.hext (fun y => ℓ.extendObj_of_mem b₀ y.2)
    fun y z d => ?_) fun x hx s t hs ht => ?_
  · have hg : grade ℕ ((inclMap M) d.1) = 1 := ((isMorphism (incl M)).grade_eq d.1).trans d.2.1
    simp only [Labelling.comap, Prefunctor.comp_map]
    rw [Map.freePrefunctor_map_of_grade_eq _ d hg]
    refine (heq_of_eq (ℓ.extendPrefunctor_map_of_mem b₀ @edge ((inclMap M).mapEdge d hg)
      d.1.2)).trans ?_
    exact Quiver.homOfEq_heq _ _ _
  · refine (conjEqToHom_comap_cell (inclMap M) _ hx
      (fun d _ => (isMorphism (incl M)).grade_eq d) hs ht).heq.trans ?_
    exact (ℓ.extend_cell_heq_of_mem b₀ @edge cell (hP := hP) x.2 _ _ _).trans
      (ℓ.cell_heq_of_eq rfl _ _ _ _ _ _)

end Labelling

end Extension

namespace Labelling

theorem isCommutativeAt_of_pathCell_eq {ℓ : Labelling B P hP} {y : P}
    (h : ∀ {s t : P} (hs : P.boundary (.Iic y) 0 false = .Iic s)
      (ht : P.boundary (.Iic y) 0 true = .Iic t) {xs ys : List P}
      (hxs : IsLayerOrder (P.boundary (.Iic y) 2 false) xs)
      (hys : IsLayerOrder (P.boundary (.Iic y) 2 true) ys),
      ℓ.pathCell ((hP y).boundary 2 false) hxs
          (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
          (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) =
        ℓ.pathCell ((hP y).boundary 2 true) hys
          (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
          (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht)) :
    ℓ.IsCommutativeAt y := by
  intro s t hs ht xs ys hxs hys
  obtain ⟨-, -, -, -, hhom⟩ := PathCell.mk.inj (h hs ht hxs hys)
  exact eq_of_heq (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
    ((((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans
      (hhom.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))).trans
      ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm))

theorem IsCommutativeAt.pathCell_eq {ℓ : Labelling B P hP} {y : P} (h : ℓ.IsCommutativeAt y)
    {s t : P} (hs : P.boundary (.Iic y) 0 false = .Iic s)
    (ht : P.boundary (.Iic y) 0 true = .Iic t) {xs ys : List P}
    (hxs : IsLayerOrder (P.boundary (.Iic y) 2 false) xs)
    (hys : IsLayerOrder (P.boundary (.Iic y) 2 true) ys) :
    ℓ.pathCell ((hP y).boundary 2 false) hxs
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) =
      ℓ.pathCell ((hP y).boundary 2 true) hys
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans hs)
        (((hP y).isGlobular.boundary_boundary_eq_of_le zero_le_two (.inl two_pos)).trans ht) :=
  PathCell.ext rfl rfl
    (heq_of_eq (congrArg _ (pathOf_congr ((boundary_one_boundary_two (hP y) false false).trans
      (boundary_one_boundary_two (hP y) true false).symm))))
    (heq_of_eq (congrArg _ (pathOf_congr ((boundary_one_boundary_two (hP y) false true).trans
      (boundary_one_boundary_two (hP y) true true).symm))))
    (((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
      ((((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm.trans
        ((h hs ht hxs hys).heq.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)))).trans
        ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm))

variable {Q : OGP.{u}} [Fintype Q] [DecidableLE Q] {hQ : Q.IsRDC}

theorem IsCommutativeAt.of_comap (f : P ⟶ Q) [IsInclusion f] {ℓ : Labelling B Q hQ} {y : P}
    (h : (ℓ.comap ⟨f, isMap_of_isInclusion f⟩ hP).IsCommutativeAt y) :
    ℓ.IsCommutativeAt (f y) := by
  classical
  refine isCommutativeAt_of_pathCell_eq ?_
  intro _ _ _ _ _ _ _ _
  have hs := boundary_zero_eq_Iic_vertex _ (hP y) false
  have ht := boundary_zero_eq_Iic_vertex _ (hP y) true
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le ((hP y).boundary 2 false)
    ((krullDim_boundary_le _ 2 false).trans_eq Nat.cast_ofNat)
  obtain ⟨ys, hys⟩ := exists_isLayerOrder_of_krullDim_le ((hP y).boundary 2 true)
    ((krullDim_boundary_le _ 2 true).trans_eq Nat.cast_ofNat)
  have hb (α : Bool) : map f (P.boundary (.Iic y) 2 α) = Q.boundary (.Iic (f y)) 2 α := by
    rw [map_boundary, map_Iic]
  have e := h.pathCell_eq hs ht hxs hys
  rw [pathCell_comap_of_isInclusion, pathCell_comap_of_isInclusion] at e
  exact (ℓ.pathCell_congr (hb false).symm _ _ _ _ _ _ _ _).trans
    (e.trans (ℓ.pathCell_congr (hb true) _ _ _ _ _ _ _ _))

end Labelling

end Atoms.Molecule.OGP
