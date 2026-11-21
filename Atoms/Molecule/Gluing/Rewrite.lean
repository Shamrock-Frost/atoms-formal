import Atoms.ForMathlib.Data.FinEnum.Option
import Atoms.Molecule.Gluing.Finite
import Atoms.Molecule.Submolecule

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {U V : OGP.{u}}

def _root_.CategoryTheory.Iso.IsSigned {A : LowerSet U} {B : LowerSet V}
    (φ : U.restrict (U.bdryFull A) ≅ V.restrict (V.bdryFull B)) : Prop :=
  ∀ (α : Bool) (x : U.restrict (U.bdryFull A)),
    incl (U.bdryFull A) x ∈ U.bdry A α ↔ incl (V.bdryFull B) (φ.hom x) ∈ V.bdry B α

variable (n : ℕ) (φ : U.restrict (U.bdryFull ⊤) ≅ V.restrict (V.bdryFull ⊤))

namespace rewrite

private theorem exists_le_grade_eq {P : OGP.{u}} (hP : P.IsRound ⊤) (hd : krullDim P = n)
    (x : P) : ∃ y, x ≤ y ∧ grade ℕ y = n := by
  obtain ⟨y, hxy, hy⟩ := GradeOrder.exists_le_maximal (s := (⊤ : LowerSet P))
    (fun y _ => krullDim_le_coe_iff.1 hd.le y) (mem_univ x)
  exact ⟨y, hxy, hP.grade_eq_of_maximal (by rwa [LowerSet.krullDim_top]) hy⟩

private theorem notMem_bdryFull_of_grade_eq {P : OGP.{u}} (hd : krullDim P = n) {x : P}
    (hx : grade ℕ x = n) : x ∉ P.bdryFull ⊤ := by
  rintro (h | h) <;>
    exact ((grade_lt_of_mem_bdry h).trans_le (by rw [LowerSet.krullDim_top, hd])).ne (by rw [hx])

variable {φ}

private theorem exists_le_grade_eq_glue (hU : U.IsRound ⊤) (hV : V.IsRound ⊤)
    (hUd : krullDim U = n) (hVd : krullDim V = n) (x : glue φ) :
    ∃ y, x ≤ y ∧ grade ℕ y = n := by
  have key {P : OGP.{u}} (f : P ⟶ glue φ) (hP : P.IsRound ⊤) (hd : krullDim P = n) (p : P) :
      ∃ y, f p ≤ y ∧ grade ℕ y = n := by
    obtain ⟨q, hpq, hq⟩ := exists_le_grade_eq n hP hd p
    exact ⟨f q, (isMorphism f).monotone hpq, ((isMorphism f).grade_eq q).trans hq⟩
  rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · exact key _ hU hUd p
  · exact key _ hV hVd q

private theorem grade_le_of_glue (hUd : krullDim U = n) (hVd : krullDim V = n) (x : glue φ) :
    grade ℕ x ≤ n := by
  rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · exact ((isMorphism _).grade_eq p).trans_le (krullDim_le_coe_iff.1 hUd.le p)
  · exact ((isMorphism _).grade_eq q).trans_le (krullDim_le_coe_iff.1 hVd.le q)

private theorem isMax_iff_grade_eq (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n)
    (hVd : krullDim V = n) {x : glue φ} : IsMax x ↔ grade ℕ x = n := by
  constructor
  · intro hx
    obtain ⟨y, hxy, hy⟩ := exists_le_grade_eq_glue n hU hV hUd hVd x
    rw [le_antisymm hxy (hx hxy)]
    exact hy
  · intro hx y hxy
    exact (GradeOrder.eq_of_le_of_grade_le hxy (by rw [hx]; exact grade_le_of_glue n hUd hVd y)).ge

private def topOrient (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n)
    (hVd : krullDim V = n) (y : glue φ) :
    (y : WithTop (glue φ)) ⋖ ⊤ → {b : Bool // b = true ↔ ∃ v, glue.inr φ v = y} :=
  Quot.recOnSubsingleton y fun (a : U ⊕ V) => match a with
    | .inl u => fun (h : ((glue.inl φ u : glue φ) : WithTop (glue φ)) ⋖ ⊤) =>
      ⟨false, iff_of_false Bool.false_ne_true fun ⟨_, hv⟩ =>
        notMem_bdryFull_of_grade_eq n hUd (((isMorphism (glue.inl φ)).grade_eq u).symm.trans
          ((isMax_iff_grade_eq n hU hV hUd hVd).1 (WithTop.coe_covBy_top.1 h)))
          (glue.inl_eq_inr_iff.1 hv.symm).fst⟩
    | .inr v => fun _ => ⟨true, iff_of_true rfl ⟨v, rfl⟩⟩

private abbrev gradeMinOrder (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n)
    (hVd : krullDim V = n) : GradeMinOrder ℕ (WithTop (glue φ)) where
  grade
    | ⊤ => n + 1
    | (x : glue φ) => grade ℕ x
  grade_strictMono a b h := by
    obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 h.ne_top
    rcases b with _ | y
    · exact Nat.lt_succ_of_le (grade_le_of_glue n hUd hVd x)
    · exact grade_strictMono (WithTop.coe_lt_coe.1 h)
  covBy_grade a b h := by
    obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 h.lt.ne_top
    rcases b with _ | y
    · exact Nat.covBy_iff_add_one_eq.2
        (congrArg (· + 1) ((isMax_iff_grade_eq n hU hV hUd hVd).1 (WithTop.coe_covBy_top.1 h)))
    · exact (WithTop.coe_covBy_coe.1 h).grade ℕ
  isMin_grade a h := by
    rcases a with _ | x
    · obtain ⟨u, -⟩ := exists_grade_eq_of_krullDim_eq hUd
      exact (h.not_lt (WithTop.coe_lt_top (glue.inl φ u))).elim
    · have hx : IsMin x := fun y hy => WithTop.coe_le_coe.1 (h (WithTop.coe_le_coe.2 hy))
      exact hx.grade ℕ

private def orient (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n)
    (hVd : krullDim V = n) : ∀ x y : WithTop (glue φ), y ⋖ x → Bool
  | (_ : glue φ), (_ : glue φ), h => (glue φ).orient (WithTop.coe_covBy_coe.1 h)
  | ⊤, (y : glue φ), h => (topOrient n hU hV hUd hVd y h).1
  | (_ : glue φ), ⊤, h => (not_top_lt h.lt).elim
  | ⊤, ⊤, h => (h.ne rfl).elim

end rewrite

def rewrite (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n) (hVd : krullDim V = n) :
    OGP.{u} where
  carrier := WithTop (glue φ)
  gradeMinOrderCarrier := rewrite.gradeMinOrder n hU hV hUd hVd
  orient {x y} h := rewrite.orient n hU hV hUd hVd x y h

namespace rewrite

variable (hU : U.IsRound ⊤) (hV : V.IsRound ⊤) (hUd : krullDim U = n) (hVd : krullDim V = n)

transfer_instances rewrite n φ hU hV hUd hVd with OrderTop

variable {n φ hU hV hUd hVd} in
@[coe] def base (x : glue φ) : rewrite n φ hU hV hUd hVd := (x : WithTop (glue φ))

instance : Coe (glue φ) (rewrite n φ hU hV hUd hVd) := ⟨base⟩

@[simp] theorem base_inj {x y : glue φ} :
    (base x : rewrite n φ hU hV hUd hVd) = base y ↔ x = y :=
  WithTop.coe_eq_coe

transfer_instances rewrite n φ hU hV hUd hVd with FinEnum DecidableLE DecidableEq

@[simp] theorem grade_top : grade ℕ (⊤ : rewrite n φ hU hV hUd hVd) = n + 1 := rfl

def ι : glue φ ⟶ rewrite n φ hU hV hUd hVd :=
  ConcreteCategory.ofHom ⟨WithTop.coeInitialSeg (glue φ),
    .of_initialSeg (Q := rewrite n φ hU hV hUd hVd) (WithTop.coeInitialSeg (glue φ)) fun _ => rfl⟩

instance : IsInclusion (ι n φ hU hV hUd hVd) := ⟨WithTop.coe_injective⟩

def inl : U ⟶ rewrite n φ hU hV hUd hVd := glue.inl φ ≫ ι n φ hU hV hUd hVd

def inr : V ⟶ rewrite n φ hU hV hUd hVd := glue.inr φ ≫ ι n φ hU hV hUd hVd

instance : IsInclusion (inl n φ hU hV hUd hVd) :=
  inferInstanceAs (IsInclusion (glue.inl φ ≫ ι n φ hU hV hUd hVd))

instance : IsInclusion (inr n φ hU hV hUd hVd) :=
  inferInstanceAs (IsInclusion (glue.inr φ ≫ ι n φ hU hV hUd hVd))

theorem inl_apply (x : U) : inl n φ hU hV hUd hVd x = base (glue.inl φ x) := rfl

theorem inr_apply (x : V) : inr n φ hU hV hUd hVd x = base (glue.inr φ x) := rfl

@[reassoc] theorem condition :
    incl (U.bdryFull ⊤) ≫ inl n φ hU hV hUd hVd =
      (φ.hom ≫ incl (V.bdryFull ⊤)) ≫ inr n φ hU hV hUd hVd :=
  glue.condition_assoc φ _

theorem inl_eq_inr_iff {x : U} {y : V} :
    inl n φ hU hV hUd hVd x = inr n φ hU hV hUd hVd y ↔
      ∃ h : x ∈ U.bdryFull ⊤, (incl (V.bdryFull ⊤) (φ.hom ⟨x, h⟩) : V) = y := by
  rw [inl_apply, inr_apply, base_inj, glue.inl_eq_inr_iff]
  rfl

theorem map_inl_sup_map_inr :
    map (inl n φ hU hV hUd hVd) ⊤ ⊔ map (inr n φ hU hV hUd hVd) ⊤ =
      map (ι n φ hU hV hUd hVd) ⊤ := by
  rw [inl, inr, map_comp, map_comp, ← map_sup, glue.map_inl_sup_map_inr]

theorem map_inl_inf_map_inr :
    map (inl n φ hU hV hUd hVd) ⊤ ⊓ map (inr n φ hU hV hUd hVd) ⊤ =
      map (inl n φ hU hV hUd hVd) (U.bdryFull ⊤) := by
  rw [inl, inr, map_comp, map_comp, ← map_inf, glue.map_inl_inf_map_inr, map_comp, map_incl_top,
    map_comp]

theorem mem_range_ι_or_eq_top (x : rewrite n φ hU hV hUd hVd) :
    x ∈ range (ι n φ hU hV hUd hVd) ∨ x = ⊤ := by
  rcases x with _ | x
  · exact .inr rfl
  · exact .inl ⟨x, rfl⟩

theorem faces_false_top :
    (rewrite n φ hU hV hUd hVd).faces false ⊤ = inl n φ hU hV hUd hVd '' {x | grade ℕ x = n} := by
  ext z
  rw [mem_faces]
  constructor
  · rintro ⟨hc, ho⟩
    obtain ⟨y, rfl⟩ := WithTop.ne_top_iff_exists.1 hc.lt.ne_top
    have hy := (isMax_iff_grade_eq n hU hV hUd hVd).1 (WithTop.coe_covBy_top.1 hc)
    rcases glue.exists_inl_or_inr y with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · exact ⟨u, ((isMorphism _).grade_eq u).symm.trans hy, rfl⟩
    · exact absurd ((topOrient n hU hV hUd hVd _ hc).2.2 ⟨v, rfl⟩)
        fun h => Bool.false_ne_true (ho.symm.trans h)
  · rintro ⟨x, hx, rfl⟩
    have hc : (glue.inl φ x : WithTop (glue φ)) ⋖ ⊤ := WithTop.coe_covBy_top.2
      ((isMax_iff_grade_eq n hU hV hUd hVd).2 (((isMorphism _).grade_eq x).trans hx))
    refine ⟨hc, Bool.eq_false_iff.2 fun ht => ?_⟩
    obtain ⟨v, hv⟩ := (topOrient n hU hV hUd hVd _ hc).2.1 ht
    exact notMem_bdryFull_of_grade_eq n hUd hx (glue.inl_eq_inr_iff.1 hv.symm).fst

theorem faces_true_top :
    (rewrite n φ hU hV hUd hVd).faces true ⊤ = inr n φ hU hV hUd hVd '' {x | grade ℕ x = n} := by
  ext z
  rw [mem_faces]
  constructor
  · rintro ⟨hc, ho⟩
    obtain ⟨y, rfl⟩ := WithTop.ne_top_iff_exists.1 hc.lt.ne_top
    obtain ⟨v, rfl⟩ := (topOrient n hU hV hUd hVd _ hc).2.1 ho
    exact ⟨v, ((isMorphism _).grade_eq v).symm.trans
      ((isMax_iff_grade_eq n hU hV hUd hVd).1 (WithTop.coe_covBy_top.1 hc)), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hc : (glue.inr φ x : WithTop (glue φ)) ⋖ ⊤ := WithTop.coe_covBy_top.2
      ((isMax_iff_grade_eq n hU hV hUd hVd).2 (((isMorphism _).grade_eq x).trans hx))
    exact ⟨hc, (topOrient n hU hV hUd hVd _ hc).2.2 ⟨x, rfl⟩⟩

theorem top_eq_Iic : (⊤ : LowerSet (rewrite n φ hU hV hUd hVd)) = .Iic ⊤ := LowerSet.Iic_top.symm

theorem krullDim_eq : krullDim (rewrite n φ hU hV hUd hVd) = n + 1 := by
  rw [← LowerSet.krullDim_top, top_eq_Iic, LowerSet.krullDim_Iic, grade_top]
  push_cast
  rfl

private theorem lowerClosure_image_grade_eq {P Q : OGP.{u}} (f : P ⟶ Q) (hP : P.IsRound ⊤)
    (hd : krullDim P = n) : lowerClosure (f '' {x | grade ℕ x = n}) = map f ⊤ := by
  refine SetLike.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨_, ⟨x, -, rfl⟩, hyx⟩ := mem_lowerClosure.1 hy
    obtain ⟨z, -, rfl⟩ := (isMorphism f).fibration hyx
    exact ⟨z, trivial, rfl⟩
  · obtain ⟨x, -, rfl⟩ := hy
    obtain ⟨z, hxz, hz⟩ := exists_le_grade_eq n hP hd x
    exact mem_lowerClosure.2 ⟨f z, ⟨z, hz, rfl⟩, (isMorphism f).monotone hxz⟩

private theorem bdry_top (α : Bool) :
    (rewrite n φ hU hV hUd hVd).bdry ⊤ α =
      lowerClosure ((rewrite n φ hU hV hUd hVd).faces α ⊤) := by
  rw [top_eq_Iic, bdry_Iic]

theorem bdry_top_false :
    (rewrite n φ hU hV hUd hVd).bdry ⊤ false = map (inl n φ hU hV hUd hVd) ⊤ := by
  rw [bdry_top, faces_false_top, lowerClosure_image_grade_eq n _ hU hUd]

theorem bdry_top_true :
    (rewrite n φ hU hV hUd hVd).bdry ⊤ true = map (inr n φ hU hV hUd hVd) ⊤ := by
  rw [bdry_top, faces_true_top, lowerClosure_image_grade_eq n _ hV hVd]

theorem map_ι_top : map (ι n φ hU hV hUd hVd) ⊤ = (rewrite n φ hU hV hUd hVd).bdryFull ⊤ := by
  simp only [OGP.bdryFull, bdry_top_false, bdry_top_true, map_inl_sup_map_inr]

theorem map_inl_bdry (hφ : φ.IsSigned) (α : Bool) :
    map (inl n φ hU hV hUd hVd) (U.bdry ⊤ α) = map (inr n φ hU hV hUd hVd) (V.bdry ⊤ α) := by
  have hc (x : U.restrict (U.bdryFull ⊤)) :
      inl n φ hU hV hUd hVd (incl _ x) = inr n φ hU hV hUd hVd (incl _ (φ.hom x)) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (condition n φ hU hV hUd hVd) x
  have hle {W : OGP.{u}} {y : W} (hy : y ∈ W.bdry ⊤ α) : y ∈ W.bdryFull ⊤ :=
    bdry_le_bdryFull ⊤ α hy
  refine SetLike.ext fun z => ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (hφ α ⟨x, hle hx⟩).1 hx, (hc ⟨x, hle hx⟩).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hw : φ.hom (φ.inv ⟨y, hle hy⟩) = ⟨y, hle hy⟩ := Iso.inv_hom_id_apply φ _
    have hyw : incl _ (φ.hom (φ.inv ⟨y, hle hy⟩)) ∈ V.bdry ⊤ α := by
      rw [hw]
      exact hy
    refine ⟨_, (hφ α (φ.inv ⟨y, hle hy⟩)).2 hyw, ?_⟩
    rw [hc, hw]
    rfl

theorem isRound_top (hφ : φ.IsSigned) : (rewrite n φ hU hV hUd hVd).IsRound ⊤ := by
  have hb (α : Bool) : (rewrite n φ hU hV hUd hVd).bdry (.Iic ⊤) α =
      cond α (map (inr n φ hU hV hUd hVd) ⊤) (map (inl n φ hU hV hUd hVd) ⊤) := by
    rw [← top_eq_Iic]
    cases α
    · exact bdry_top_false n φ hU hV hUd hVd
    · exact bdry_top_true n φ hU hV hUd hVd
  rw [top_eq_Iic]
  refine isRound_Iic_of_halves (grade_top n φ hU hV hUd hVd) (fun α => ?_) (fun α => ?_)
    (fun α => ?_) ?_
  · obtain ⟨u, hu⟩ := exists_grade_eq_of_krullDim_eq hUd
    obtain ⟨v, hv⟩ := exists_grade_eq_of_krullDim_eq hVd
    rw [hb]
    cases α
    · exact ⟨inl n φ hU hV hUd hVd u, u, trivial, rfl⟩
    · exact ⟨inr n φ hU hV hUd hVd v, v, trivial, rfl⟩
  · rw [hb]
    cases α
    · exact (isRound_map_iff _ ⊤).2 hU
    · exact (isRound_map_iff _ ⊤).2 hV
  · rw [hb, hb]
    exact (map_bdry _ ⊤ α).symm.trans ((map_inl_bdry n φ hU hV hUd hVd hφ α).trans (map_bdry _ ⊤ α))
  · rw [hb, hb]
    exact (map_inl_inf_map_inr n φ hU hV hUd hVd).trans (map_bdryFull _ ⊤)

theorem isMolecule (hφ : φ.IsSigned) (hUm : IsMolecule U) (hVm : IsMolecule V) :
    IsMolecule (rewrite n φ hU hV hUd hVd) := by
  have hr := isRound_top n φ hU hV hUd hVd hφ
  rw [top_eq_Iic] at hr
  refine (?_ : IsMoleculeIn _ ⊤)
  rw [top_eq_Iic]
  refine .atom _ hr fun α => ?_
  rw [← top_eq_Iic]
  cases α
  · rw [bdry_top_false]
    exact (isMoleculeIn_map_iff _ ⊤).2 hUm
  · rw [bdry_top_true]
    exact (isMoleculeIn_map_iff _ ⊤).2 hVm

theorem isAtom (hφ : φ.IsSigned) (hUm : IsMolecule U) (hVm : IsMolecule V) :
    IsAtom (rewrite n φ hU hV hUd hVd) :=
  ⟨isMolecule n φ hU hV hUd hVd hφ hUm hVm, _, top_eq_Iic n φ hU hV hUd hVd⟩

end rewrite

end Atoms.Molecule.OGP
