import Atoms.Shape.Cone.Basic

open CategoryTheory Simplicial Order Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

def IsCore (B : Atom) : Prop := ∀ (B' : Atom) (r : ℕ), IsEmpty (B ≅ cone B' (r + 1))

theorem IsCore.of_iso {B B' : Atom} (hB : IsCore B) (e : B ≅ B') : IsCore B' :=
  fun B'' r => ⟨fun e' => (hB B'' r).false (e ≪≫ e')⟩

theorem exists_isCore_iso_cone (U : Atom) :
    ∃ (B : Atom) (r : ℕ), IsCore B ∧ Nonempty (U ≅ cone B r) := by
  induction h : U.dimension using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    by_cases hU : IsCore U
    · exact ⟨U, 0, hU, ⟨CategoryTheory.Iso.refl _⟩⟩
    · simp only [IsCore, not_forall, not_isEmpty_iff] at hU
      obtain ⟨B', r, ⟨e⟩⟩ := hU
      have hd : B'.dimension < n := by
        rw [← h, Atom.dimension_eq_of_iso e, dimension_cone]
        omega
      obtain ⟨B, k, hB, ⟨e'⟩⟩ := ih _ hd B' rfl
      exact ⟨B, k + (r + 1), hB, ⟨e ≪≫ (coneFunctor (r + 1)).mapIso e' ≪≫ coneAssoc B k (r + 1)⟩⟩

theorem eq_and_nonempty_iso_of_iso_cone {B B' : Atom} {r r' : ℕ} (hB : IsCore B)
    (hB' : IsCore B') (e : cone B r ≅ cone B' r') : r = r' ∧ Nonempty (B ≅ B') := by
  induction r generalizing r' with
  | zero =>
    cases r' with
    | zero => exact ⟨rfl, ⟨e⟩⟩
    | succ r' => exact ((hB B' r').false e).elim
  | succ r ih =>
    cases r' with
    | zero => exact ((hB' B r).false e.symm).elim
    | succ r' =>
      obtain ⟨e'⟩ := nonempty_iso_of_iso_cone_one (X := cone B r) (Y := cone B' r') e
      obtain ⟨h₁, h₂⟩ := ih e'
      exact ⟨congrArg (· + 1) h₁, h₂⟩

theorem isCore_iff_dimension_eq_zero {B : Atom} (hd : B.dimension ≤ 1) :
    IsCore B ↔ B.dimension = 0 := by
  refine ⟨fun hB => by_contra fun h0 => ?_, fun h0 B' r => ⟨fun e => ?_⟩⟩
  · obtain ⟨e₁⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one (U := B) (by omega)
    obtain ⟨e₂⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one
      (U := atomJoin atomPoint atomPoint) (by rw [dimension_atomJoin, dimension_atomPoint])
    exact (hB atomPoint 0).false (e₁.symm ≪≫ e₂)
  · have := Atom.dimension_eq_of_iso e
    rw [dimension_cone] at this
    omega

theorem exists_isInclusionHom_cone_one_apply_top {B : Atom} {r : ℕ} (x : (cone B r).ogp)
    (hS : (coneCoord B r x).2.Nonempty) (hd : 0 < grade ℕ x) :
    ∃ (C : Atom) (ι : cone C 1 ⟶ cone B r), IsInclusionHom ι ∧ ι (cone C 1).top = x := by
  set S := (coneCoord B r x).2
  set j := S.max' hS
  have hjr : j.1 + 1 ≤ r := j.2
  let σ : Fin (j.1 + 1) →o Fin r := ⟨Fin.castLE hjr, fun _ _ h => h⟩
  have hσ : Function.Injective σ := Fin.castLE_injective hjr
  set T := S.preimage σ hσ.injOn
  have hT : T.image σ = S := by
    rw [Finset.image_preimage, Finset.filter_true_of_mem]
    exact fun k hk => ⟨⟨k.1, Nat.lt_succ_of_le (S.le_max' k hk)⟩, Fin.ext rfl⟩
  have hlast : Fin.last j.1 ∈ T := Finset.mem_preimage.2 (S.max'_mem hS)
  obtain ⟨y, hy⟩ := exists_coneCoord_eq_of_ne B (j.1 + 1) (coneCoord B r x).1 T
    fun h => Finset.notMem_empty _ ((Prod.mk.inj h).2 ▸ hlast)
  have hκ : coneHom B σ y = x := by
    refine eq_of_coneCoord_eq ?_
    rw [← WithBot.map_coe, coneCoord_coneHom, hy, hT]
  have hp := coneCoord_succ_coe B j.1 y
  generalize ((FiniteOGP.ofOGPIso (join (cone B j.1).ogp atomPoint.ogp)).inv y).1 = q at hp
  obtain ⟨q₁, q₂⟩ := q
  have hT' : T = (conePairCoord B j.1 q₁ q₂).2 :=
    (congrArg Prod.snd hy).symm.trans (congrArg Prod.snd hp)
  have hq₂ : q₂ ≠ ⊥ := last_mem_conePairCoord_iff.1 (hT' ▸ hlast)
  obtain ⟨a, rfl⟩ : ∃ a : (cone B j.1).ogp, (a : WithBot _) = q₁ := by
    refine WithBot.ne_bot_iff_exists.1 fun h => ?_
    subst h
    have hdim := grade_cone_add_one B r x
    have hx1 : (coneCoord B r x).1 = ⊥ :=
      (congrArg Prod.fst hy).symm.trans ((congrArg Prod.fst hp).trans (by simp [conePairCoord]))
    have hT1 : T = {Fin.last j.1} := by
      rw [hT']
      simp [conePairCoord, hq₂]
    have hS1 : S.card = 1 := by
      rw [← hT, hT1, Finset.image_singleton, Finset.card_singleton]
    rw [hx1, hS1, grade_bot, Nat.bot_eq_zero] at hdim
    omega
  refine ⟨Atom.ofClosure (cone B j.1) a,
    joinHom (Atom.closureIncl (cone B j.1) a) (𝟙 atomPoint) ≫ coneHom B σ,
    fun u v h => isInclusionHom_joinHom (Atom.isInclusionHom_closureIncl _ a)
      (fun _ _ h => h) (isInclusionHom_coneHom B hσ h), ?_⟩
  refine Eq.trans (congrArg (coneHom B σ) (eq_of_coneCoord_eq (F := B) (r := j.1 + 1) ?_)) hκ
  refine (coneCoord_joinHom (B := Atom.ofClosure (cone B j.1) a) (r := 0)
    (Atom.closureIncl (cone B j.1) a) (cone (Atom.ofClosure (cone B j.1) a) 1).top).trans ?_
  have htop := coneCoord_top (Atom.ofClosure (cone B j.1) a) 1
  rw [coneCoord_succ_coe] at htop
  generalize ((FiniteOGP.ofOGPIso (join (cone (Atom.ofClosure (cone B j.1) a) 0).ogp
    atomPoint.ogp)).inv (cone (Atom.ofClosure (cone B j.1) a) 1).top) = t at htop ⊢
  obtain ⟨⟨t₁, t₂⟩, ht⟩ := t
  simp only [conePairCoord, coneCoord_zero, Finset.map_empty, Finset.empty_union] at htop
  have h₁ : t₁ = _ := congrArg Prod.fst htop
  have h₂ : (if t₂ = ⊥ then ∅ else {Fin.last 0}) = Finset.univ := congrArg Prod.snd htop
  have ht₂ : t₂ ≠ ⊥ := fun h => by simp [h] at h₂
  subst h₁
  rw [hp]
  have hmap : WithBot.map (Atom.closureIncl (cone B j.1) a)
      ((Atom.ofClosure (cone B j.1) a).top : WithBot (Atom.ofClosure (cone B j.1) a).ogp)
      = (a : WithBot (cone B j.1).ogp) := by
    rw [WithBot.map_coe, Atom.closureIncl_top]
  simp only [conePairCoord, ht₂, hq₂, if_false]
  exact congrArg (fun w => ((coneCoord B j.1 w).1,
    (coneCoord B j.1 w).2.map Fin.castSuccEmb ∪ {Fin.last j.1})) hmap

theorem nonempty_iso_ofClosure_of_isInclusionHom {T U : Atom} {ι : T ⟶ U}
    (hι : IsInclusionHom ι) : Nonempty (T ≅ Atom.ofClosure U (ι T.top)) := by
  have huniv : Set.Iic T.top = Set.univ := Set.eq_univ_of_forall T.le_top
  have hrange : Set.range ι = Set.Iic (ι T.top) := by
    rw [← Set.image_univ, ← huniv, (Atom.isMap ι).image_Iic T.top]
  obtain ⟨e, -⟩ := exists_iso_comp_closureIncl ι hrange
    (by rw [T.dimension_eq, grade_eq_of_isInclusionHom ι hι])
  exact ⟨e⟩

theorem coneCoord_snd_eq_empty_of_iso {F B : Atom} {r : ℕ} (hF : IsCore F)
    (hF0 : 0 < F.dimension) {z : (cone B r).ogp}
    (e : F ≅ Atom.ofClosure (cone B r) z) : (coneCoord B r z).2 = ∅ := by
  by_contra hS
  have hd : 0 < grade ℕ z := by
    rw [← Atom.dimension_ofClosure, ← Atom.dimension_eq_of_iso e]
    exact hF0
  obtain ⟨C, ι, hι, htop⟩ :=
    exists_isInclusionHom_cone_one_apply_top z (Finset.nonempty_iff_ne_empty.2 hS) hd
  obtain ⟨e'⟩ := nonempty_iso_ofClosure_of_isInclusionHom hι
  rw [htop] at e'
  exact (hF C 0).false (e ≪≫ e'.symm)

theorem dimension_le_of_isInclusionHom_cone {B B' : Atom} {r r' : ℕ}
    (hB' : IsCore B') (f : cone B' r' ⟶ cone B r) (hf : IsInclusionHom f) :
    B'.dimension ≤ B.dimension := by
  induction r' with
  | zero =>
    rcases Nat.eq_zero_or_pos B'.dimension with h0 | hpos
    · omega
    obtain ⟨e⟩ := nonempty_iso_ofClosure_of_isInclusionHom hf
    obtain ⟨b, hb⟩ := exists_coneIncl_eq_of_coneCoord_snd_eq_empty
      (coneCoord_snd_eq_empty_of_iso hB' hpos e)
    have hdim := grade_eq_of_isInclusionHom f hf (cone B' 0).top
    rw [← hb, grade_eq_of_isInclusionHom _ (isInclusionHom_coneIncl B r)] at hdim
    exact B'.dimension_eq.trans_le (hdim.symm.trans_le (B.grade_le_dimension b))
  | succ k ih =>
    exact ih (joinInclLeftHom (cone B' k) atomPoint ≫ f)
      (fun _ _ h => isInclusionHom_joinInclLeftHom _ _ (hf h))

theorem dimension_le_of_isCollapseHom_cone {B B' : Atom} {r r' : ℕ}
    (hB' : IsCore B') (f : cone B r ⟶ cone B' r') (hf : IsCollapseHom f) :
    B'.dimension ≤ B.dimension := by
  have := isSplitEpi_of_isCollapseHom f hf
  exact dimension_le_of_isInclusionHom_cone hB' (section_ f) (isInclusionHom_of_mono _)

theorem nonempty_iso_cone_atomSimplex_of_dimension_eq_zero {C : Atom}
    (h0 : C.dimension = 0) (j : ℕ) : Nonempty (cone C j ≅ atomSimplex j) :=
  have := isIso_toAtomPoint_of_dimension_eq_zero h0
  ⟨(coneFunctor j).mapIso (asIso (toAtomPoint C)) ≪≫ coneAtomPointIso j⟩

theorem exists_nonempty_iso_cone_simplexFunctor_obj {B : Atom} (hB : B.dimension ≤ 1)
    (r : ℕ) : ∃ k : SimplexCategory, Nonempty (cone B r ≅ simplexFunctor.obj k) := by
  obtain ⟨C, j, hC, ⟨e⟩⟩ := exists_isCore_iso_cone B
  have hd := Atom.dimension_eq_of_iso e
  rw [dimension_cone] at hd
  have h0 := (isCore_iff_dimension_eq_zero (by omega)).1 hC
  obtain ⟨φ⟩ := nonempty_iso_cone_atomSimplex_of_dimension_eq_zero h0 (j + r)
  exact ⟨⦋j + r⦌, ⟨(coneFunctor r).mapIso e ≪≫ coneAssoc C j r ≪≫ φ⟩⟩

theorem exists_nonempty_iso_simplexFunctor_obj_of_isInclusionHom {V : Atom}
    {n : SimplexCategory} (i : V ⟶ simplexFunctor.obj n) (hi : IsInclusionHom i) :
    ∃ k : SimplexCategory, Nonempty (V ≅ simplexFunctor.obj k) := by
  obtain ⟨C, j, hC, ⟨e⟩⟩ := exists_isCore_iso_cone V
  let i' : V ⟶ atomSimplex n.len := i
  have : Mono i' := mono_of_isInclusionHom i hi
  have hd := dimension_le_of_isInclusionHom_cone hC (e.inv ≫ i' ≫ (coneAtomPointIso n.len).inv)
    (isInclusionHom_of_mono _)
  rw [dimension_atomPoint] at hd
  obtain ⟨φ⟩ := nonempty_iso_cone_atomSimplex_of_dimension_eq_zero (Nat.le_zero.1 hd) j
  exact ⟨⦋j⦌, ⟨e ≪≫ φ⟩⟩

theorem exists_nonempty_iso_simplexFunctor_obj_of_isCollapseHom {V : Atom}
    {n : SimplexCategory} (p : simplexFunctor.obj n ⟶ V) (hp : IsCollapseHom p) :
    ∃ k : SimplexCategory, Nonempty (V ≅ simplexFunctor.obj k) :=
  have := isSplitEpi_of_isCollapseHom p hp
  exists_nonempty_iso_simplexFunctor_obj_of_isInclusionHom (section_ p) (isInclusionHom_of_mono _)

theorem joinInclLeftHom_comp_ne_id {F : Atom} (hF : IsCore F) (hd : 0 < F.dimension)
    (ρ : cone F 1 ⟶ F) : joinInclLeftHom F atomPoint ≫ ρ ≠ 𝟙 F := by
  intro h
  set base : (cone F 1).ogp := joinInclLeftHom F atomPoint F.top
  have hρbase : ρ base = F.top := ConcreteCategory.congr_hom h F.top
  have hρT : ρ (cone F 1).top = F.top :=
    le_antisymm (F.le_top _) (hρbase ▸ (Atom.isMap ρ).monotone ((cone F 1).le_top base))
  have hdT : grade ℕ (cone F 1).top = grade ℕ F.top + 1 := by
    rw [← (cone F 1).dimension_eq, dimension_cone, F.dimension_eq]
  have hdbase : grade ℕ base = grade ℕ F.top :=
    grade_eq_of_isInclusionHom _ (isInclusionHom_joinInclLeftHom F atomPoint) F.top
  have hbaseT : base ⋖ (cone F 1).top := by
    obtain ⟨c, hbc, hcT⟩ := exists_covBy_le_of_lt
      (lt_of_le_of_ne ((cone F 1).le_top base) fun he => by rw [he] at hdbase; omega)
    have hgc := Nat.covBy_iff_add_one_eq.1 (hbc.grade ℕ)
    exact (GradeOrder.eq_of_le_of_grade_le hcT (by omega)) ▸ hbc
  set β := !(cone F 1).ogp.orient hbaseT
  have himg := (Atom.isMap ρ).image_boundary (cone F 1).top (grade ℕ F.top) β
  have hbF : F.ogp.boundary (.Iic F.top) (grade ℕ F.top) β = .Iic F.top :=
    boundary_eq_self (by rw [LowerSet.krullDim_Iic]) β
  rw [hρT, hbF] at himg
  have hmem : F.top ∈ ρ '' ((cone F 1).ogp.boundary (.Iic (cone F 1).top) (grade ℕ F.top) β) := by
    rw [himg]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨y, hy, hρy⟩ := hmem
  rw [boundary_Iic hdT β, SetLike.mem_coe, mem_lowerClosure] at hy
  obtain ⟨z, ⟨hzT, hzβ⟩, hyz⟩ := hy
  have hρz : ρ z = F.top := le_antisymm (F.le_top _) (hρy ▸ (Atom.isMap ρ).monotone hyz)
  have hdz : grade ℕ z = grade ℕ F.top := by
    have := Nat.covBy_iff_add_one_eq.1 (hzT.grade ℕ)
    omega
  have hzS : (coneCoord F 1 z).2 ≠ ∅ := by
    intro hS
    obtain ⟨b, hb⟩ := exists_coneIncl_eq_of_coneCoord_snd_eq_empty hS
    have hdb := grade_eq_of_isInclusionHom _ (isInclusionHom_coneIncl F 1) b
    rw [hb, hdz] at hdb
    have hbt : b = F.top := GradeOrder.eq_of_le_of_grade_le (F.le_top b) hdb.le
    have hzb : z = base := by rw [← hb, hbt]; rfl
    have hcongr := (cone F 1).ogp.orient_congr rfl hzb hzT hbaseT
    rw [hzβ] at hcongr
    exact Bool.not_ne_self _ hcongr
  have hcol : IsCollapseHom (Atom.closureIncl (cone F 1) z ≫ ρ) :=
    isCollapseHom_of_apply_eq_top _ (t := (Atom.ofClosure (cone F 1) z).top)
      (by rw [ConcreteCategory.comp_apply, Atom.closureIncl_top, hρz])
  have := isIso_of_isCollapseHom_of_dimension_eq _ hcol
    (by rw [Atom.dimension_ofClosure, hdz, F.dimension_eq])
  exact hzS (coneCoord_snd_eq_empty_of_iso hF hd (asIso (Atom.closureIncl (cone F 1) z ≫ ρ)).symm)

theorem atomSimplexVertices_coneAtomPointIso (r : ℕ) (y : (cone atomPoint r).ogp) :
    atomSimplexVertices r ((coneAtomPointIso r).hom y) =
      conePointVertices r (coneCoord atomPoint r y) :=
  botVertices_coneAtomPointIso r y

theorem atomSimplexVertices_coneAtomPointIso_conePoint (m : ℕ) (j : Fin m)
    (d : atomPoint.ogp) :
    atomSimplexVertices m ((coneAtomPointIso m).hom (conePoint atomPoint m j d)) =
      {j.succ} := by
  rw [atomSimplexVertices_coneAtomPointIso, coneCoord_conePoint, conePointVertices]
  simp

theorem atomSimplexVertices_coneAtomPointIso_coneIncl (m : ℕ) (d : atomPoint.ogp) :
    atomSimplexVertices m ((coneAtomPointIso m).hom (coneIncl atomPoint m d)) = {0} := by
  rw [atomSimplexVertices_coneAtomPointIso, coneCoord_coneIncl, conePointVertices]
  simp

theorem exists_atomSimplexVertices_apply_conePoint {B : Atom} {r s : ℕ}
    (q : cone B r ⟶ atomSimplex s) (i : Fin r) :
    ∃ j, atomSimplexVertices s (q (conePoint B r i default)) = {j} := by
  refine Finset.card_eq_one.1 ?_
  have h₁ := (Atom.isMap q).grade_le (conePoint B r i default)
  have h₂ := grade_cone_add_one B r (conePoint B r i default)
  rw [coneCoord_conePoint, grade_bot, Nat.bot_eq_zero, Finset.card_singleton] at h₂
  rw [card_atomSimplexVertices]
  omega

private theorem exists_conePoint_le_mem_boundary_of_le (B : Atom) {r : ℕ} {i i' : Fin r}
    (hii' : i ≤ i') :
    ∃ e : (cone B r).ogp, conePoint B r i default ≤ e ∧
      conePoint B r i' default ∈ (cone B r).ogp.boundary (.Iic e) 0 true := by
  obtain ⟨e, hew⟩ := exists_coneCoord_eq_of_ne B r ⊥ {i, i'} fun h =>
    absurd (Prod.mk.inj h).2 (by simp)
  have hS : (coneCoord B r e).2.Nonempty := by
    rw [hew]
    exact Finset.insert_nonempty _ _
  have hmax : (coneCoord B r e).2.max' hS = i' := by
    simp only [hew]
    exact le_antisymm (Finset.max'_le _ _ _ (by simp [hii'])) (Finset.le_max' _ _ (by simp))
  refine ⟨e, ?_, hmax ▸ conePoint_mem_boundary_zero_true hS⟩
  rw [le_iff_coneCoord, coneCoord_conePoint, hew]
  exact ⟨bot_le, by simp⟩

theorem monotone_of_atomSimplexVertices_conePoint {B : Atom} {r s : ℕ}
    (q : cone B r ⟶ atomSimplex s) (τ : Fin r → Fin (s + 1))
    (hτ : ∀ i, atomSimplexVertices s (q (conePoint B r i default)) = {τ i}) :
    Monotone τ := by
  intro i i' hii'
  obtain ⟨e, hle, hb⟩ := exists_conePoint_le_mem_boundary_of_le B hii'
  have hv := Set.mem_image_of_mem q hb
  rw [(Atom.isMap q).image_boundary] at hv
  have hi := atomSimplexVertices_subset_iff.2 ((Atom.isMap q).monotone hle)
  rw [hτ i, Finset.singleton_subset_iff] at hi
  exact le_of_mem_boundary_zero_true_atomSimplex hv (hτ i') hi

theorem mem_atomSimplexVertices_apply_coneIncl_top {B : Atom} {r s : ℕ}
    (q : cone B r ⟶ atomSimplex s) (hq : IsCollapseHom q) (τ : Fin r → Fin (s + 1))
    (hτ : ∀ i, atomSimplexVertices s (q (conePoint B r i default)) = {τ i})
    {j : Fin (s + 1)} (hj : ∀ i, τ i ≠ j) :
    j ∈ atomSimplexVertices s (q (coneIncl B r B.top)) := by
  obtain ⟨d, hd⟩ := exists_atomSimplexVertices_eq s (Finset.singleton_nonempty j)
  obtain ⟨w, hw⟩ := hq d
  obtain ⟨z, -, hz, hdz⟩ := (Atom.isMap q).exists_le_apply_eq w
  rw [hw] at hz hdz
  have hdd := card_atomSimplexVertices d
  rw [hd, Finset.card_singleton] at hdd
  rcases exists_eq_of_grade_eq_zero_cone (v := z) (by omega) with ⟨b, rfl⟩ | ⟨i, rfl⟩
  · have h := atomSimplexVertices_subset_iff.2
      ((Atom.isMap q).monotone ((Atom.isMap (coneIncl B r)).monotone (B.le_top b)))
    rwa [hz, hd, Finset.singleton_subset_iff] at h
  · have h := hτ i
    rw [hz, hd, Finset.singleton_inj] at h
    exact (hj i h.symm).elim

private theorem exists_coneIncl_top_le_conePoint_mem_boundary (B : Atom) {r : ℕ} (i : Fin r) :
    ∃ w : (cone B r).ogp, coneIncl B r B.top ≤ w ∧ conePoint B r i default ≤ w ∧
      conePoint B r i default ∈ (cone B r).ogp.boundary (.Iic w) 0 true := by
  obtain ⟨w, hew⟩ := exists_coneCoord_eq_of_ne B r (B.top : WithBot _) {i} fun h =>
    absurd (Prod.mk.inj h).1 (by simp)
  have hS : (coneCoord B r w).2.Nonempty := by
    rw [hew]
    exact Finset.singleton_nonempty i
  have hmax : (coneCoord B r w).2.max' hS = i := by
    simp only [hew]
    exact Finset.max'_singleton i
  refine ⟨w, ?_, ?_, hmax ▸ conePoint_mem_boundary_zero_true hS⟩
  · rw [le_iff_coneCoord, coneCoord_coneIncl, hew]
    exact ⟨le_rfl, Finset.empty_subset _⟩
  · rw [le_iff_coneCoord, coneCoord_conePoint, hew]
    exact ⟨bot_le, le_rfl⟩

theorem le_of_mem_atomSimplexVertices_apply_coneIncl_top {B : Atom} {r s : ℕ}
    (q : cone B r ⟶ atomSimplex s) (τ : Fin r → Fin (s + 1))
    (hτ : ∀ i, atomSimplexVertices s (q (conePoint B r i default)) = {τ i})
    {j : Fin (s + 1)} (hj : j ∈ atomSimplexVertices s (q (coneIncl B r B.top)))
    (i : Fin r) : j ≤ τ i := by
  obtain ⟨w, hle, -, hb⟩ := exists_coneIncl_top_le_conePoint_mem_boundary B i
  have hv := Set.mem_image_of_mem q hb
  rw [(Atom.isMap q).image_boundary] at hv
  exact le_of_mem_boundary_zero_true_atomSimplex hv (hτ i)
    (atomSimplexVertices_subset_iff.2 ((Atom.isMap q).monotone hle) hj)

theorem exists_apply_coneIncl_eq_coneIncl_top {B F : Atom} {r s : ℕ} (hF : IsCore F)
    (hF0 : 0 < F.dimension) (q : cone B r ⟶ cone F s) (hq : IsCollapseHom q) :
    ∃ b, q (coneIncl B r b) = coneIncl F s F.top ∧
      grade ℕ b = F.dimension := by
  set t := coneIncl F s F.top
  obtain ⟨w, hw⟩ := hq t
  obtain ⟨z, -, hz, hdz⟩ := (Atom.isMap q).exists_le_apply_eq w
  rw [hw] at hz hdz
  have hdt : grade ℕ t = F.dimension := by
    rw [grade_eq_of_isInclusionHom _ (isInclusionHom_coneIncl F s), F.dimension_eq]
  have hval : ∀ u, ∃ f, coneIncl F s f = (Atom.closureIncl (cone B r) z ≫ q) u := by
    intro u
    refine exists_coneIncl_eq_of_coneCoord_snd_eq_empty ?_
    have hle : (Atom.closureIncl (cone B r) z ≫ q) u ≤ t := by
      rw [ConcreteCategory.comp_apply, ← hz]
      exact (Atom.isMap q).monotone (closureIncl_mem_closure _ z u)
    have := (le_iff_coneCoord.1 hle).2
    rw [coneCoord_coneIncl] at this
    exact Finset.subset_empty.1 this
  obtain ⟨g, hg⟩ := exists_comp_eq_of_isInclusionHom _ (isInclusionHom_coneIncl F s) _ hval
  have hgtop : g (Atom.ofClosure (cone B r) z).top = F.top := by
    refine isInclusionHom_coneIncl F s ?_
    rw [← ConcreteCategory.comp_apply, hg, ConcreteCategory.comp_apply, Atom.closureIncl_top, hz]
  have := isIso_of_isCollapseHom_of_dimension_eq g (isCollapseHom_of_apply_eq_top g hgtop)
    (by rw [Atom.dimension_ofClosure, hdz, hdt])
  obtain ⟨b, hb⟩ := exists_coneIncl_eq_of_coneCoord_snd_eq_empty
    (coneCoord_snd_eq_empty_of_iso hF hF0 (asIso g).symm)
  refine ⟨b, hb ▸ hz, ?_⟩
  rw [← grade_eq_of_isInclusionHom _ (isInclusionHom_coneIncl B r) b, hb, hdz, hdt]

theorem exists_conePoint_comp_eq {B F : Atom} {r s : ℕ} (hF : IsCore F)
    (hF0 : 0 < F.dimension) (q : cone B r ⟶ cone F s) (hq : IsCollapseHom q) (i : Fin r) :
    ∃ j, conePoint B r i ≫ q = conePoint F s j := by
  obtain ⟨b, hbt, hdb⟩ := exists_apply_coneIncl_eq_coneIncl_top hF hF0 q hq
  set v := q (conePoint B r i default)
  suffices hS : (coneCoord F s v).2 ≠ ∅ by
    have h1 := (Atom.isMap q).grade_le (conePoint B r i default)
    have h3 := grade_cone_add_one B r (conePoint B r i default)
    rw [coneCoord_conePoint, grade_bot, Nat.bot_eq_zero, Finset.card_singleton] at h3
    obtain ⟨b, hb⟩ | ⟨j, hj⟩ :=
      exists_eq_of_grade_eq_zero_cone (v := v) (Nat.le_zero.1 (h1.trans (by omega)))
    · exact absurd (by rw [← hb, coneCoord_coneIncl]) hS
    · exact ⟨j, Atom.hom_ext fun u => by rw [Subsingleton.elim u default]; exact hj.symm⟩
  intro hS
  set C := Atom.ofClosure B b
  let σ₁ : Fin 1 →o Fin r := ⟨fun _ => i, fun _ _ _ => le_rfl⟩
  let ι := coneMap (Atom.closureIncl B b) 1 ≫ coneHom B σ₁
  have hιbase : joinInclLeftHom C atomPoint ≫ ι = Atom.closureIncl B b ≫ coneIncl B r := by
    have h := coneIncl_comp_coneMap_assoc (Atom.closureIncl B b) 1 (coneHom B σ₁)
    rw [coneIncl_comp_coneHom] at h
    exact (Category.id_comp _).symm.trans h
  set w := ι (cone C 1).top
  have hw : coneCoord B r w = ((b : WithBot B.ogp), {i}) := by
    have h1 := coneCoord_coneHom B σ₁
      (WithBot.some (coneMap (Atom.closureIncl B b) 1 (cone C 1).top))
    have h2 := coneCoord_coneMap (Atom.closureIncl B b) 1 (WithBot.some (cone C 1).top)
    rw [coneCoord_top, WithBot.map_coe] at h2
    rw [WithBot.map_coe, h2] at h1
    refine h1.trans (Prod.ext ?_ ?_)
    · exact congrArg WithBot.some (Atom.closureIncl_top B b)
    · ext j
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  have hiw : conePoint B r i default ∈
      (cone B r).ogp.boundary (.Iic w) 0 true := by
    obtain ⟨u, hu⟩ := boundary_closure_nonempty (cone B r) w 0 true
    have hS1 : (coneCoord B r w).2.Nonempty := by
      rw [hw]
      exact Finset.singleton_nonempty i
    have hcu := coneCoord_of_mem_boundary_zero_true hS1 hu
    have hu' : u = conePoint B r i default :=
      eq_of_coneCoord_eq (by rw [coneCoord_conePoint, hcu]; simp [hw])
    exact hu' ▸ hu
  have hqw : (coneCoord F s (q w)).2 = ∅ := by
    by_contra hT
    have hv : v ∈ (cone F s).ogp.boundary (.Iic (q w)) 0 true := by
      rw [← SetLike.mem_coe, ← (Atom.isMap q).image_boundary]
      exact Set.mem_image_of_mem _ hiw
    have := coneCoord_of_mem_boundary_zero_true (Finset.nonempty_iff_ne_empty.2 hT) hv
    rw [this] at hS
    exact Finset.singleton_ne_empty _ hS
  have hval : ∀ u, ∃ f, coneIncl F s f = (ι ≫ q) u := fun u => by
    refine exists_coneIncl_eq_of_coneCoord_snd_eq_empty ?_
    have hle : (ι ≫ q) u ≤ q w :=
      (Atom.isMap q).monotone ((Atom.isMap ι).monotone ((cone C 1).le_top u))
    have := (le_iff_coneCoord.1 hle).2
    rw [hqw] at this
    exact Finset.subset_empty.1 this
  obtain ⟨ρ', hρ'⟩ := exists_comp_eq_of_isInclusionHom _ (isInclusionHom_coneIncl F s) _ hval
  set φ := joinInclLeftHom C atomPoint ≫ ρ'
  have hφtop : φ C.top = F.top := by
    refine isInclusionHom_coneIncl F s ?_
    have h1 := ConcreteCategory.congr_hom hρ' (joinInclLeftHom C atomPoint C.top)
    have h2 := ConcreteCategory.congr_hom hιbase C.top
    refine h1.trans ((congrArg q h2).trans ?_)
    rw [ConcreteCategory.comp_apply, Atom.closureIncl_top, hbt]
  obtain ⟨ψ, -, hψ⟩ := (isIso_of_isCollapseHom_of_dimension_eq φ
    (isCollapseHom_of_apply_eq_top φ hφtop) (by rw [Atom.dimension_ofClosure, hdb])).out
  refine joinInclLeftHom_comp_ne_id hF hF0 (joinHom ψ (𝟙 atomPoint) ≫ ρ') ?_
  exact (joinInclLeftHom_comp_joinHom_assoc ψ (𝟙 atomPoint) ρ').trans hψ

theorem pos_of_isCollapseHom {B F : Atom} {r s : ℕ} (hF : IsCore F)
    (hF0 : 0 < F.dimension) (hr : 0 < r) (q : cone B r ⟶ cone F s)
    (hq : IsCollapseHom q) : 0 < s :=
  (exists_conePoint_comp_eq hF hF0 q hq ⟨0, hr⟩).choose.pos

private theorem succ_mem_atomSimplexVertices_iff {F : Atom} {s : ℕ} (x : (cone F s).ogp)
    (j : Fin s) :
    j.succ ∈ atomSimplexVertices s ((coneMap (toAtomPoint F) s ≫ (coneAtomPointIso s).hom) x) ↔
      j ∈ (coneCoord F s x).2 := by
  rw [ConcreteCategory.comp_apply, atomSimplexVertices_coneAtomPointIso, ← WithBot.map_coe,
    coneCoord_coneMap, conePointVertices]
  split_ifs <;> simp [Fin.succ_ne_zero]

private theorem atomSimplexVertices_comp_conePoint {B F : Atom} {r s : ℕ}
    (h : cone B r ⟶ cone F s) (τ : Fin r → Fin s)
    (hτ : ∀ i, conePoint B r i ≫ h = conePoint F s (τ i)) (i : Fin r) :
    atomSimplexVertices s ((h ≫ coneMap (toAtomPoint F) s ≫ (coneAtomPointIso s).hom)
      (conePoint B r i default)) = {(τ i).succ} := by
  rw [← ConcreteCategory.comp_apply (conePoint B r i), reassoc_of% (hτ i),
    conePoint_comp_coneMap_assoc, ConcreteCategory.comp_apply,
    atomSimplexVertices_coneAtomPointIso_conePoint]

theorem monotone_of_comp_conePoint {B F : Atom} {r s : ℕ} (h : cone B r ⟶ cone F s)
    (τ : Fin r → Fin s) (hτ : ∀ i, conePoint B r i ≫ h = conePoint F s (τ i)) : Monotone τ :=
  fun _ _ hii' => Fin.succ_le_succ_iff.1 (monotone_of_atomSimplexVertices_conePoint _ _
    (atomSimplexVertices_comp_conePoint h τ hτ) hii')

theorem mem_coneCoord_apply_coneIncl_top {B F : Atom} {r s : ℕ} (q : cone B r ⟶ cone F s)
    (hq : IsCollapseHom q) (τ : Fin r → Fin s)
    (hτ : ∀ i, conePoint B r i ≫ q = conePoint F s (τ i)) {j : Fin s} (hj : ∀ i, τ i ≠ j) :
    j ∈ (coneCoord F s (q (coneIncl B r B.top))).2 :=
  (succ_mem_atomSimplexVertices_iff _ j).1 (mem_atomSimplexVertices_apply_coneIncl_top _
    (collapses.comp_mem _ _ hq (collapses.comp_mem _ _
      (isCollapseHom_coneMap _ (isCollapseHom_toAtomPoint F) s) (isCollapseHom_of_iso _)))
    _ (atomSimplexVertices_comp_conePoint q τ hτ) fun i h => hj i (Fin.succ_injective _ h))

theorem le_of_mem_coneCoord_apply_coneIncl_top {B F : Atom} {r s : ℕ} (q : cone B r ⟶ cone F s)
    (τ : Fin r → Fin s) (hτ : ∀ i, conePoint B r i ≫ q = conePoint F s (τ i)) {j : Fin s}
    (hj : j ∈ (coneCoord F s (q (coneIncl B r B.top))).2) (i : Fin r) : j ≤ τ i :=
  Fin.succ_le_succ_iff.1 (le_of_mem_atomSimplexVertices_apply_coneIncl_top _ _
    (atomSimplexVertices_comp_conePoint q τ hτ) ((succ_mem_atomSimplexVertices_iff _ j).2 hj) i)

private theorem mem_iff_lt_card_of_forall_ne {n r : ℕ} {τ : Fin r → Fin n} {K : Finset (Fin n)}
    (hP₁ : ∀ j, (∀ i, τ i ≠ j) → j ∈ K) (hP₂ : ∀ j ∈ K, ∀ i, j ≤ τ i) (j : Fin n) :
    j ∈ K ↔ j.1 < K.card := by
  have hdown : ∀ j ∈ K, ∀ j' ≤ j, j' ∈ K := fun j hj j' hj' => by_contra fun hj'K => by
    obtain ⟨i, hi⟩ := not_forall_not.1 (mt (hP₁ j') hj'K)
    exact hj'K (le_antisymm hj' (hi ▸ hP₂ j hj i) ▸ hj)
  refine ⟨fun hj => ?_, fun hj => by_contra fun hjK => ?_⟩
  · have h := Finset.card_le_card fun j' hj' => hdown j hj j' (Finset.mem_Iic.1 hj')
    rw [Fin.card_Iic] at h
    omega
  · have h := Finset.card_le_card fun j' (hj' : j' ∈ K) =>
      Finset.mem_Iio.2 (lt_of_not_ge fun h => hjK (hdown j' hj' j h))
    rw [Fin.card_Iio] at h
    omega

theorem exists_coneHom_factorization {B F : Atom} {r s : ℕ} (hF : IsCore F)
    (hF0 : 0 < F.dimension) (q : cone B r ⟶ cone F s) (hq : IsCollapseHom q) :
    ∃ (k : ℕ) (hk : k ≤ s) (q₀ : B ⟶ cone F k) (σ : Fin (k + r) →o Fin s),
      IsCollapseHom q₀ ∧ Function.Surjective σ ∧
        (∀ i : Fin k, σ (Fin.castAdd r i) = Fin.castLE hk i) ∧
          q = coneMap q₀ r ≫ (coneAssoc F k r).hom ≫ coneHom F σ := by
  choose τ hτ using exists_conePoint_comp_eq hF hF0 q hq
  set y := q (coneIncl B r B.top)
  set K := (coneCoord F s y).2
  have hP₁ : ∀ j, (∀ i, τ i ≠ j) → j ∈ K := fun j hj =>
    mem_coneCoord_apply_coneIncl_top q hq τ hτ hj
  have hP₂ : ∀ j ∈ K, ∀ i, j ≤ τ i := fun j hj i =>
    le_of_mem_coneCoord_apply_coneIncl_top q τ hτ hj i
  set k := K.card
  have hK : ∀ j : Fin s, j ∈ K ↔ j.1 < k := mem_iff_lt_card_of_forall_ne hP₁ hP₂
  have hk : k ≤ s := (Finset.card_le_univ K).trans (Fintype.card_fin s).le
  let ι : Fin k →o Fin s := ⟨Fin.castLE hk, fun _ _ h => h⟩
  have hι : Function.Injective ι := Fin.castLE_injective hk
  have hKι : K = Finset.univ.image ι := Finset.ext fun j => (hK j).trans
    ⟨fun h => Finset.mem_image.2 ⟨⟨j.1, h⟩, Finset.mem_univ _, Fin.ext rfl⟩, fun h => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
      exact a.2⟩
  obtain ⟨q₀, hq₀⟩ := exists_comp_coneHom_eq (coneIncl B r ≫ q) hι hKι.subset
  obtain ⟨b, hbt, -⟩ := exists_apply_coneIncl_eq_coneIncl_top hF hF0 q hq
  have hy₁ : (coneCoord F s y).1 = F.top := by
    have h :=
      (le_iff_coneCoord.1 ((Atom.isMap q).monotone ((Atom.isMap (coneIncl B r)).monotone
        (B.le_top b)))).1
    rw [hbt, coneCoord_coneIncl] at h
    exact le_antisymm (WithBot.le_coe_iff.2 fun f _ => F.le_top f) h
  have hq₀top : q₀ B.top = (cone F k).top := by
    have h := ConcreteCategory.congr_hom hq₀ B.top
    have h' := congrArg (fun x : (cone F s).ogp => coneCoord F s x) h
    simp only [ConcreteCategory.comp_apply] at h'
    rw [← WithBot.map_coe, coneCoord_coneHom, Prod.mk.injEq] at h'
    refine eq_of_coneCoord_eq ?_
    rw [coneCoord_top]
    exact Prod.ext (h'.1.trans hy₁) (Finset.image_injective hι (h'.2.trans hKι))
  obtain ⟨σ, hσs, hσl, hσr⟩ := Fin.exists_surjective_orderHom_castAdd_natAdd hk
    (monotone_of_comp_conePoint q τ hτ) (fun a i => hP₂ _ ((hK _).2 a.2) i)
    fun j hj => not_forall_not.1 fun h => absurd ((hK j).1 (hP₁ j h)) (by omega)
  have hσι : σ.comp ⟨Fin.castAdd r, fun _ _ h => h⟩ = ι := OrderHom.ext _ _ (funext hσl)
  refine ⟨k, hk, q₀, σ, isCollapseHom_of_apply_eq_top q₀ hq₀top, hσs, hσl, ?_⟩
  refine Atom.hom_ext fun z => eq_of_coneCoord_eq ?_
  rw [coneCoord_apply_of_comp_conePoint q τ hτ z,
    coneCoord_apply_of_comp_conePoint _ τ
      (fun i => (conePoint_comp_coneMap_comp_coneHom q₀ σ i).trans
        (congrArg (conePoint F s) (hσr i))) z, coneIncl_comp_coneMap_comp_coneHom, hσι, hq₀]

theorem eq_of_coneHom_factorization {B F : Atom} {r s k k' : ℕ} (hk : k ≤ s) (hk' : k' ≤ s)
    {q₀ : B ⟶ cone F k} {q₀' : B ⟶ cone F k'} (hq₀ : IsCollapseHom q₀)
    (hq₀' : IsCollapseHom q₀') {σ : Fin (k + r) →o Fin s} {σ' : Fin (k' + r) →o Fin s}
    (hσ : ∀ i : Fin k, σ (Fin.castAdd r i) = Fin.castLE hk i)
    (hσ' : ∀ i : Fin k', σ' (Fin.castAdd r i) = Fin.castLE hk' i)
    (h : coneMap q₀ r ≫ (coneAssoc F k r).hom ≫ coneHom F σ =
      coneMap q₀' r ≫ (coneAssoc F k' r).hom ≫ coneHom F σ') :
    k = k' ∧ ∀ i : Fin r, σ (Fin.natAdd k i) = σ' (Fin.natAdd k' i) := by
  have himage : ∀ {m : ℕ} (hm : m ≤ s) (p : B ⟶ cone F m) (τ : Fin (m + r) →o Fin s),
      IsCollapseHom p → (∀ i : Fin m, τ (Fin.castAdd r i) = Fin.castLE hm i) →
      coneCoord F s ((coneIncl B r ≫ coneMap p r ≫ (coneAssoc F m r).hom ≫ coneHom F τ) B.top)
        = ((F.top : WithBot F.ogp), Finset.univ.image (Fin.castLE hm)) := by
    intro m hm p τ hp hτ
    have hpt : p B.top = (cone F m).top :=
      hp.apply_top
    rw [coneIncl_comp_coneMap_comp_coneHom, ConcreteCategory.comp_apply, hpt, ← WithBot.map_coe,
      coneCoord_coneHom, coneCoord_top]
    refine Prod.ext rfl (Finset.image_congr fun i _ => hτ i)
  refine ⟨?_, fun i => ?_⟩
  · have h₁ := himage hk q₀ σ hq₀ hσ
    rw [h, himage hk' q₀' σ' hq₀' hσ', Prod.mk.injEq] at h₁
    have h₂ := congrArg Finset.card h₁.2
    rwa [Finset.card_image_of_injective _ (Fin.castLE_injective _),
      Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_univ,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, eq_comm] at h₂
  · have h₁ := congrArg (conePoint B r i ≫ ·) h
    simp only [conePoint_comp_coneMap_comp_coneHom] at h₁
    have h₂ := congrArg (fun f : atomPoint ⟶ cone F s => coneCoord F s (f default)) h₁
    simp only [coneCoord_conePoint, Prod.mk.injEq, Finset.singleton_inj, true_and] at h₂
    exact h₂

theorem boundary_closure_top_zero_false_cone (F : Atom) (r : ℕ) :
    ((cone F r).ogp.boundary (.Iic (cone F r).top) 0 false : Set (cone F r).ogp) =
      coneIncl F r '' (F.ogp.boundary (.Iic F.top) 0 false : Set F.ogp) := by
  induction r with
  | zero => exact (Set.image_id _).symm
  | succ r ih =>
    let e : join (cone F r).ogp atomPoint.ogp ≅ (cone F (r + 1)).ogp :=
      FiniteOGP.ofOGPIso (join (cone F r).ogp atomPoint.ogp)
    obtain ⟨p, hp⟩ : ∃ p, e.hom p = (cone F (r + 1)).top :=
      ⟨e.inv _, ConcreteCategory.congr_hom e.inv_hom_id _⟩
    have hcc := coneCoord_succ_ofOGPIso F r p
    change coneCoord F (r + 1) (e.hom p) = _ at hcc
    rw [hp, coneCoord_top] at hcc
    have hp₁ : p.1.1 = ((cone F r).top : WithBot _) := by
      refine coneCoord_injective F r ?_
      rw [coneCoord_top]
      refine Prod.ext (congrArg Prod.fst hcc).symm (Finset.eq_univ_of_forall fun i => ?_)
      have : Fin.castSucc i ∈ (conePairCoord F r p.1.1 p.1.2).2 := by
        rw [← hcc]
        exact Finset.mem_univ _
      exact castSucc_mem_conePairCoord_iff.1 this
    have hb := (isMap_of_isInclusion e.hom).image_boundary p 0 false
    rw [boundary_Iic_join_zero_false p _ hp₁, coe_map, Set.image_image, hp] at hb
    refine hb.symm.trans ?_
    rw [ih, Set.image_image]
    rfl

theorem boundary_closure_zero_false_cone {B : Atom} {r : ℕ} (y : (cone B r).ogp)
    {b : B.ogp} (hb : (coneCoord B r y).1 = b) :
    ((cone B r).ogp.boundary (.Iic y) 0 false : Set (cone B r).ogp) =
      coneIncl B r '' (B.ogp.boundary (.Iic b) 0 false : Set B.ogp) := by
  obtain ⟨S, hS⟩ : ∃ S, (coneCoord B r y).2 = S := ⟨_, rfl⟩
  let ε : Fin S.card →o Fin r := (S.orderEmbOfFin rfl).toOrderHom
  let C := Atom.ofClosure B b
  let φ : cone C S.card ⟶ cone B r := coneHom C ε ≫ coneMap (Atom.closureIncl B b) r
  have hφ : φ (cone C S.card).top = y := by
    refine eq_of_coneCoord_eq ?_
    have h₁ := coneCoord_coneHom C ε ((cone C S.card).top : WithBot _)
    rw [WithBot.map_coe, coneCoord_top] at h₁
    have h₂ := coneCoord_coneMap (Atom.closureIncl B b) r
      (coneHom C ε (cone C S.card).top : WithBot _)
    rw [WithBot.map_coe, h₁] at h₂
    refine h₂.trans (Prod.ext ?_ ?_)
    · rw [WithBot.map_coe, Atom.closureIncl_top, hb]
    · rw [hS]
      change Finset.univ.image (S.orderEmbOfFin rfl) = S
      rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Finset.range_orderEmbOfFin]
  have hcomp : coneIncl C S.card ≫ φ = Atom.closureIncl B b ≫ coneIncl B r := by
    rw [coneIncl_comp_coneHom_assoc, coneIncl_comp_coneMap]
  have h₃ := (Atom.isMap φ).image_boundary (cone C S.card).top 0 false
  rw [hφ, boundary_closure_top_zero_false_cone, Set.image_image] at h₃
  rw [← h₃]
  have h₄ := (Atom.isMap (Atom.closureIncl B b)).image_boundary C.top 0 false
  rw [Atom.closureIncl_top] at h₄
  rw [← h₄, Set.image_image]
  exact congrArg (fun g : C ⟶ cone B r =>
    g '' (C.ogp.boundary (.Iic C.top) 0 false : Set C.ogp)) hcomp

theorem exists_iso_coneIncl_comp_eq {B F : Atom} {r s : ℕ} (hF : IsCore F)
    (hd : B.dimension = F.dimension) (q : cone B r ⟶ cone F s)
    (hq : IsCollapseHom q) : ∃ e : B ≅ F, coneIncl B r ≫ q = e.hom ≫ coneIncl F s := by
  rcases Nat.eq_zero_or_pos F.dimension with h0 | hpos
  · have hB0 : B.dimension = 0 := hd.trans h0
    have hx : ∀ U : Atom, U.dimension = 0 → ∀ x : U.ogp, x = U.top :=
      fun U hU x => GradeOrder.eq_of_le_of_grade_le (U.le_top x)
        (by rw [← U.dimension_eq, hU]; omega)
    have hpt : ∀ U : Atom, U.dimension = 0 →
        (U.ogp.boundary (.Iic U.top) 0 false : Set U.ogp) = {U.top} := by
      intro U hU
      have hcl : U.ogp.boundary (.Iic U.top) 0 false = .Iic U.top :=
        boundary_eq_self (by rw [LowerSet.krullDim_Iic, ← U.dimension_eq, hU, Nat.cast_zero]) false
      rw [hcl]
      exact Set.eq_singleton_iff_unique_mem.2 ⟨LowerSet.mem_Iic_iff.2 le_rfl, fun x _ => hx U hU x⟩
    have := isIso_toAtomPoint_of_dimension_eq_zero hB0
    have := isIso_toAtomPoint_of_dimension_eq_zero h0
    refine ⟨asIso (toAtomPoint B) ≪≫ (asIso (toAtomPoint F)).symm, Atom.hom_ext fun x => ?_⟩
    rw [hx B hB0 x, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    refine (?_ : _ = coneIncl F s F.top).trans (congrArg (coneIncl F s) (hx F h0 _)).symm
    have hqt : q (cone B r).top = (cone F s).top :=
      hq.apply_top
    have hb := (Atom.isMap q).image_boundary (cone B r).top 0 false
    rw [hqt, boundary_closure_top_zero_false_cone, boundary_closure_top_zero_false_cone,
      hpt B hB0, hpt F h0, Set.image_singleton, Set.image_singleton,
      Set.image_singleton] at hb
    exact Set.singleton_eq_singleton_iff.1 hb
  · obtain ⟨k, hk, q₀, σ, hq₀, -, -, hfac⟩ := exists_coneHom_factorization hF hpos q hq
    have hk0 : k = 0 := by
      have := dimension_le_of_isCollapseHom q₀ hq₀
      rw [dimension_cone, hd] at this
      omega
    subst hk0
    have hiso := isIso_of_isCollapseHom_of_dimension_eq q₀ hq₀ (by rw [dimension_cone, hd]; rfl)
    refine ⟨@asIso _ _ _ _ q₀ hiso, ?_⟩
    rw [hfac, coneIncl_comp_coneMap_comp_coneHom]
    rfl

private theorem exists_isCollapseHom_comp_eq_of_atomSimplexVertices {T : Atom} {k s : ℕ}
    (hk : k ≤ s) (g : T ⟶ atomSimplex s)
    (hg : atomSimplexVertices s (g T.top) = Finset.Iic ⟨k, by omega⟩) :
    ∃ q₀ : T ⟶ cone atomPoint k, IsCollapseHom q₀ ∧
      q₀ ≫ coneHom atomPoint ⟨Fin.castLE hk, fun _ _ h => h⟩ ≫ (coneAtomPointIso s).hom = g := by
  obtain ⟨q₀, hq₀⟩ := exists_comp_coneHom_eq (g ≫ (coneAtomPointIso s).inv)
    (σ := ⟨Fin.castLE hk, fun _ _ h => h⟩) (Fin.castLE_injective hk) fun j hj => by
      have h : j.succ ∈ atomSimplexVertices s (g T.top) := by
        rw [← Iso.inv_hom_id_apply (coneAtomPointIso s) (g T.top),
          atomSimplexVertices_coneAtomPointIso, conePointVertices]
        exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
      rw [hg, Finset.mem_Iic] at h
      exact Finset.mem_image.2 ⟨⟨j.1, Nat.lt_of_succ_le h⟩, Finset.mem_univ _, Fin.ext rfl⟩
  replace hq₀ : q₀ ≫ coneHom atomPoint ⟨Fin.castLE hk, fun _ _ h => h⟩ ≫
      (coneAtomPointIso s).hom = g := by
    rw [← Category.assoc, hq₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨q₀, isCollapseHom_of_apply_eq_top q₀ (GradeOrder.eq_of_le_of_grade_le
    ((cone atomPoint k).le_top (q₀ T.top)) ?_), hq₀⟩
  have h := card_atomSimplexVertices (g T.top)
  rw [hg, Fin.card_Iic, Fin.val_mk, ← hq₀, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    grade_eq_of_isInclusionHom _ (isInclusionHom_of_mono _),
    grade_eq_of_isInclusionHom _ (isInclusionHom_coneHom _ (Fin.castLE_injective hk))] at h
  rw [← (cone atomPoint k).dimension_eq, dimension_cone, dimension_atomPoint]
  omega

theorem exists_simplexHom_factorization {B : Atom} {r s : ℕ}
    (q : cone B r ⟶ atomSimplex s) (hq : IsCollapseHom q) :
    ∃ (k : ℕ) (hk : k ≤ s) (q₀ : B ⟶ cone atomPoint k)
      (σ : Fin (k + r + 1) →o Fin (s + 1)),
      IsCollapseHom q₀ ∧ Function.Surjective σ ∧
        (∀ i : Fin (k + 1), σ (Fin.castLE (by omega) i) = Fin.castLE (by omega) i) ∧
          q = coneMap q₀ r ≫ (coneAssoc atomPoint k r).hom ≫
            (coneAtomPointIso (k + r)).hom ≫ simplexHom σ := by
  choose τ hτ using exists_atomSimplexVertices_apply_conePoint q
  have hmono := monotone_of_atomSimplexVertices_conePoint q τ hτ
  set K := atomSimplexVertices s (q (coneIncl B r B.top))
  have hP₁ : ∀ j, (∀ i, τ i ≠ j) → j ∈ K := fun j hj =>
    mem_atomSimplexVertices_apply_coneIncl_top q hq τ hτ hj
  have hP₂ : ∀ j ∈ K, ∀ i, j ≤ τ i := fun j hj i =>
    le_of_mem_atomSimplexVertices_apply_coneIncl_top q τ hτ hj i
  have hKpos : 0 < K.card := Finset.card_pos.2 (simplexVertices_nonempty s _)
  set k := K.card - 1
  have hK : ∀ j : Fin (s + 1), j ∈ K ↔ j.1 ≤ k := fun j =>
    (mem_iff_lt_card_of_forall_ne hP₁ hP₂ j).trans (by omega)
  have hk : k ≤ s := by
    have := (Finset.card_le_univ K).trans (Fintype.card_fin (s + 1)).le
    omega
  let ι : Fin k →o Fin s := ⟨Fin.castLE hk, fun _ _ h => h⟩
  let ιk := coneHom atomPoint ι ≫ (coneAtomPointIso s).hom
  have hVιk : ∀ u, atomSimplexVertices s (ιk u) = conePointVertices s
      ((coneCoord atomPoint k u).1, (coneCoord atomPoint k u).2.image ι) := fun u => by
    rw [ConcreteCategory.comp_apply, atomSimplexVertices_coneAtomPointIso, ← WithBot.map_coe,
      coneCoord_coneHom]
  obtain ⟨q₀, hq₀top, hq₀⟩ := exists_isCollapseHom_comp_eq_of_atomSimplexVertices hk
    (coneIncl B r ≫ q) (Finset.ext fun j => (hK j).trans (by rw [Finset.mem_Iic, Fin.le_def]))
  obtain ⟨σ', hσs, hσl, hσr⟩ := Fin.exists_surjective_orderHom_castAdd_natAdd (k := k + 1)
    (by omega) hmono (fun a i => hP₂ _ ((hK _).2 (Nat.lt_succ_iff.1 a.2)) i)
    fun j hj => not_forall_not.1 fun h => absurd ((hK j).1 (hP₁ j h)) (by omega)
  let σ : Fin (k + r + 1) →o Fin (s + 1) := σ'.comp ⟨Fin.cast (by omega), fun _ _ h => h⟩
  have hσ : ∀ m m', m.1 = m'.1 → σ m = σ' m' := fun m m' h => congrArg σ' (Fin.ext h)
  have hσ0 : σ 0 = 0 := (hσ 0 (Fin.castAdd r 0) rfl).trans ((hσl 0).trans (Fin.ext rfl))
  have hσsucc : ∀ j : Fin k, σ (Fin.castAdd r j).succ = (ι j).succ := fun j =>
    (hσ _ (Fin.castAdd r j.succ) rfl).trans ((hσl _).trans (Fin.ext rfl))
  have hσpt : ∀ i : Fin r, σ (Fin.natAdd k i).succ = τ i := fun i =>
    (hσ _ (Fin.natAdd (k + 1) i) (by simp only [Fin.val_succ, Fin.val_natAdd]; omega)).trans
      (hσr i)
  have hface : coneIncl (cone atomPoint k) r ≫ (coneAssoc atomPoint k r).hom ≫
      (coneAtomPointIso (k + r)).hom ≫ simplexHom σ = ιk := by
    refine Atom.hom_ext fun u => atomSimplexVertices_injective s ?_
    rw [hVιk, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, atomSimplexVertices_simplexHom,
      atomSimplexVertices_coneAtomPointIso, ← WithBot.map_coe, coneCoord_coneAssoc,
      coneCoord_coneIncl]
    by_cases hb : (coneCoord atomPoint k u).1 = ⊥ <;> ext m <;>
      simp [conePointVertices, hb, hσ0, hσsucc]
  refine ⟨k, hk, q₀, σ, hq₀top, fun j => ?_,
    fun i => (hσ _ (Fin.castAdd r i) rfl).trans ((hσl i).trans (Fin.ext rfl)), ?_⟩
  · obtain ⟨m, hm⟩ := hσs j
    exact ⟨Fin.cast (by omega) m, (hσ _ m rfl).trans hm⟩
  · refine hom_ext_atomSimplex fun v hv => ?_
    rcases exists_eq_of_grade_eq_zero_cone hv with ⟨b, rfl⟩ | ⟨i, rfl⟩
    · have h₁ := ConcreteCategory.congr_hom hq₀ b
      have h₂ := ConcreteCategory.congr_hom (coneIncl_comp_coneMap_assoc q₀ r
        ((coneAssoc atomPoint k r).hom ≫ (coneAtomPointIso (k + r)).hom ≫ simplexHom σ)) b
      rw [hface] at h₂
      exact h₁.symm.trans h₂.symm
    · refine atomSimplexVertices_injective s ?_
      rw [hτ i]
      have h₂ := ConcreteCategory.congr_hom (conePoint_comp_coneMap_assoc q₀ r i
        ((coneAssoc atomPoint k r).hom ≫ (coneAtomPointIso (k + r)).hom ≫ simplexHom σ))
        default
      rw [conePoint_comp_coneAssoc_assoc] at h₂
      rw [← ConcreteCategory.comp_apply (conePoint B r i), h₂, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, atomSimplexVertices_simplexHom,
        atomSimplexVertices_coneAtomPointIso_conePoint, Finset.image_singleton, hσpt]

end Atoms.Shape
