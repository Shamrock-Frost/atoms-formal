import Atoms.Molecule.Cartesian
import Atoms.Molecule.Category

universe u

open Order Set Topology

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

private abbrev PushforwardPair (f : P → Q) : Type u := {p : P × Q // p.2 ≤ f p.1}

private def PushforwardRel (f : P → Q) (a b : PushforwardPair f) : Prop :=
  a.1.2 = b.1.2 ∧ a.1.1 ≤ b.1.1

private abbrev PushforwardCarrier (f : P → Q) : Type u := Quot (PushforwardRel f)

variable (f : P → Q)

private def pfMk (x : P) (y : Q) (h : y ≤ f x) : PushforwardCarrier f := Quot.mk _ ⟨(x, y), h⟩

private def pfLoc : PushforwardCarrier f → Q := Quot.lift (fun a => a.1.2) fun _ _ h => h.1

private def pfBelow : PushforwardCarrier f → Set (PushforwardCarrier f) :=
  Quot.lift (fun a => {w | ∃ (y : Q) (h : y ≤ a.1.2), w = pfMk f a.1.1 y (h.trans a.2)})
    fun a b hab => by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy.trans hab.1.le, Quot.sound ⟨rfl, hab.2⟩⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy.trans hab.1.ge, (Quot.sound ⟨rfl, hab.2⟩).symm⟩

variable {f}

private theorem pf_ind {p : PushforwardCarrier f → Prop} (h : ∀ x y h, p (pfMk f x y h))
    (z : PushforwardCarrier f) : p z :=
  Quot.ind (fun a => h a.1.1 a.1.2 a.2) z

private instance : PartialOrder (PushforwardCarrier f) where
  le w z := w ∈ pfBelow f z
  le_refl := pf_ind fun _ y _ => ⟨y, le_rfl, rfl⟩
  le_trans w z v hwz hzv := by
    induction v using pf_ind with
    | h x y'' h'' =>
      obtain ⟨y', hy', rfl⟩ := hzv
      obtain ⟨y, hy, rfl⟩ := hwz
      exact ⟨y, hy.trans hy', rfl⟩
  le_antisymm w z hwz hzw := by
    induction z using pf_ind with
    | h x y' h' =>
      obtain ⟨y, hy, rfl⟩ := hwz
      obtain ⟨y'', hy'', he⟩ := hzw
      have hy' : y' = y'' := congrArg (pfLoc f) he
      obtain rfl := le_antisymm hy (hy'.trans_le hy'')
      rfl

private theorem pf_le_mk_iff {w : PushforwardCarrier f} {x : P} {y' : Q} (h' : y' ≤ f x) :
    w ≤ pfMk f x y' h' ↔ ∃ (y : Q) (hy : y ≤ y'), w = pfMk f x y (hy.trans h') :=
  Iff.rfl

private theorem pfLoc_mono {w z : PushforwardCarrier f} (h : w ≤ z) : pfLoc f w ≤ pfLoc f z := by
  induction z using pf_ind with
  | h x y' h' =>
    obtain ⟨y, hy, rfl⟩ := (pf_le_mk_iff h').1 h
    exact hy

private theorem pf_eq_of_pfLoc_eq {w v z : PushforwardCarrier f} (hw : w ≤ z) (hv : v ≤ z)
    (h : pfLoc f w = pfLoc f v) : w = v := by
  induction z using pf_ind with
  | h x y' h' =>
    obtain ⟨y, hy, rfl⟩ := (pf_le_mk_iff h').1 hw
    obtain ⟨y'', hy'', rfl⟩ := (pf_le_mk_iff h').1 hv
    obtain rfl : y = y'' := h
    rfl

private theorem pf_le_of_pfLoc_le {w v z : PushforwardCarrier f} (hw : w ≤ z) (hv : v ≤ z)
    (h : pfLoc f w ≤ pfLoc f v) : w ≤ v := by
  induction z using pf_ind with
  | h x y' h' =>
    obtain ⟨y, hy, rfl⟩ := (pf_le_mk_iff h').1 hw
    obtain ⟨y'', hy'', rfl⟩ := (pf_le_mk_iff h').1 hv
    exact ⟨y, h, rfl⟩

private theorem pf_exists_le {z : PushforwardCarrier f} {c : Q} (hc : c ≤ pfLoc f z) :
    ∃ w ≤ z, pfLoc f w = c := by
  induction z using pf_ind with
  | h x y' h' => exact ⟨pfMk f x c (hc.trans h'), ⟨c, hc, rfl⟩, rfl⟩

private theorem pfLoc_lt {w z : PushforwardCarrier f} (h : w < z) : pfLoc f w < pfLoc f z :=
  (pfLoc_mono h.le).lt_of_ne fun he => h.ne (pf_eq_of_pfLoc_eq h.le le_rfl he)

private theorem pf_lt_of_pfLoc_lt {w v z : PushforwardCarrier f} (hw : w ≤ z) (hv : v ≤ z)
    (h : pfLoc f w < pfLoc f v) : w < v :=
  (pf_le_of_pfLoc_le hw hv h.le).lt_of_ne fun he => h.ne (congrArg (pfLoc f) he)

private theorem pfLoc_covBy {w z : PushforwardCarrier f} (h : w ⋖ z) : pfLoc f w ⋖ pfLoc f z := by
  refine ⟨pfLoc_lt h.lt, fun c hwc hcz => ?_⟩
  obtain ⟨v, hvz, rfl⟩ := pf_exists_le hcz.le
  exact h.2 (pf_lt_of_pfLoc_lt h.le hvz hwc) (pf_lt_of_pfLoc_lt hvz le_rfl hcz)

private theorem pf_covBy_of_pfLoc_covBy {w z : PushforwardCarrier f} (hw : w ≤ z)
    (h : pfLoc f w ⋖ pfLoc f z) : w ⋖ z :=
  ⟨pf_lt_of_pfLoc_lt hw le_rfl h.lt, fun _ hwv hvz => h.2 (pfLoc_lt hwv) (pfLoc_lt hvz)⟩

private instance : GradeMinOrder ℕ (PushforwardCarrier f) where
  grade z := grade ℕ (pfLoc f z)
  grade_strictMono _ _ h := grade_strictMono (pfLoc_lt h)
  covBy_grade _ _ h := (pfLoc_covBy h).grade ℕ
  isMin_grade w h := by
    refine IsMin.grade ℕ fun c hc => ?_
    obtain ⟨v, hvw, rfl⟩ := pf_exists_le hc
    exact pfLoc_mono (h hvw)

variable (f) in
@[nolint unusedArguments]
def pushforward (_hf : Monotone f) : OGP.{u} where
  carrier := PushforwardCarrier f
  orient h := Q.orient (pfLoc_covBy h)

variable (hf : Monotone f)

variable (f) in
def pushforwardMk (x : P) (y : Q) (h : y ≤ f x) : pushforward f hf := pfMk f x y h

variable (f) in
def pushforwardFinal : P → pushforward f hf := fun x => pushforwardMk f hf x (f x) le_rfl

variable (f) in
def pushforwardLocal : pushforward f hf → Q := pfLoc f

variable (f)

@[simp] theorem pushforwardLocal_pushforwardMk (x : P) (y : Q) (h : y ≤ f x) :
    pushforwardLocal f hf (pushforwardMk f hf x y h) = y :=
  rfl

theorem pushforwardLocal_comp_pushforwardFinal :
    pushforwardLocal f hf ∘ pushforwardFinal f hf = f :=
  rfl

theorem pushforwardMk_le_pushforwardMk_iff {x x' : P} {y y' : Q} (h : y ≤ f x) (h' : y' ≤ f x') :
    pushforwardMk f hf x y h ≤ pushforwardMk f hf x' y' h' ↔
      ∃ h'' : y ≤ f x', y ≤ y' ∧ pushforwardMk f hf x y h = pushforwardMk f hf x' y h'' := by
  refine ⟨fun hle => ?_, fun ⟨_, hy, he⟩ => ⟨y, hy, he⟩⟩
  obtain ⟨y₀, hy₀, he⟩ := (pf_le_mk_iff h').1 hle
  obtain rfl : y = y₀ := congrArg (pfLoc f) he
  exact ⟨_, hy₀, he⟩

variable {f hf} in
theorem exists_pushforwardMk_eq (z : pushforward f hf) :
    ∃ (x : P) (y : Q) (h : y ≤ f x), pushforwardMk f hf x y h = z :=
  pf_ind (p := fun z => ∃ (x : P) (y : Q) (h : y ≤ f x), pfMk f x y h = z)
    (fun x y h => ⟨x, y, h, rfl⟩) z

theorem isLocalEmbedding_pushforwardLocal : IsLocalEmbedding (pushforwardLocal f hf) := fun z => by
  have hcl : closure ({z} : Set (pushforward f hf)) = Iic z := IsUpperSet.closure_singleton
  have hmem (w : closure ({z} : Set (pushforward f hf))) : (w : pushforward f hf) ≤ z :=
    (Set.ext_iff.1 hcl w.1).1 w.2
  have hmono : Monotone ((closure ({z} : Set (pushforward f hf))).domRestrict
      (pushforwardLocal f hf)) := fun _ _ hab => pfLoc_mono (f := f) hab
  refine .of_continuous_injective_isClosedMap (IsUpperSet.monotone_iff_continuous.1 hmono)
    (fun a b h => Subtype.ext (pf_eq_of_pfLoc_eq (hmem a) (hmem b) h))
    (IsUpperSet.isClosedMap_iff_fibration.2 fun a c hc => ?_)
  obtain ⟨w, hwa, rfl⟩ := pf_exists_le (f := f) hc
  exact ⟨⟨w, (Set.ext_iff.1 hcl w).2 (le_trans (α := PushforwardCarrier f) hwa (hmem a))⟩, hwa,
    rfl⟩

theorem isMorphism_pushforwardLocal : IsMorphism (pushforwardLocal f hf) where
  bijOn_faces z α := by
    refine ⟨fun w ⟨h, hα⟩ => ⟨pfLoc_covBy h, hα⟩,
      fun w hw v hv he => pf_eq_of_pfLoc_eq hw.1.le hv.1.le he, fun c ⟨hc, hα⟩ => ?_⟩
    obtain ⟨w, hwz, rfl⟩ := pf_exists_le (f := f) hc.le
    exact ⟨w, ⟨pf_covBy_of_pfLoc_covBy hwz hc, hα⟩, rfl⟩

private theorem pushforwardMk_le_pushforwardFinal (x : P) (y : Q) (h : y ≤ f x) :
    pushforwardMk f hf x y h ≤ pushforwardFinal f hf x :=
  ⟨y, h, rfl⟩

theorem pushforwardFinal_monotone : Monotone (pushforwardFinal f hf) := fun x _ hx =>
  ⟨f x, hf hx, Quot.sound ⟨rfl, hx⟩⟩

private theorem reflTransGen_of_eqvGen {a b : PushforwardPair f}
    (h : Relation.EqvGen (PushforwardRel f) a b) :
    Relation.ReflTransGen (fun x x' =>
      x ∈ univ ∩ pushforwardFinal f hf ⁻¹' Ici (pushforwardMk f hf a.1.1 a.1.2 a.2) ∧
      x' ∈ univ ∩ pushforwardFinal f hf ⁻¹' Ici (pushforwardMk f hf a.1.1 a.1.2 a.2) ∧
      (x ≤ x' ∨ x' ≤ x)) a.1.1 b.1.1 := by
  induction h with
  | rel a b hab =>
    have he : pushforwardMk f hf a.1.1 a.1.2 a.2 = pushforwardMk f hf b.1.1 b.1.2 b.2 :=
      Quot.sound hab
    refine .single ⟨⟨trivial, pushforwardMk_le_pushforwardFinal f hf _ _ _⟩, ⟨trivial, ?_⟩,
      Or.inl hab.2⟩
    rw [he]
    exact pushforwardMk_le_pushforwardFinal f hf _ _ _
  | refl => exact .refl
  | symm a b hab ih =>
    have he : pushforwardMk f hf a.1.1 a.1.2 a.2 = pushforwardMk f hf b.1.1 b.1.2 b.2 :=
      Quot.eqvGen_sound hab
    rw [← he]
    exact Relation.ReflTransGen.mono (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩) _ _
      (Relation.ReflTransGen.swap _ _ ih)
  | trans a b c hab _ ih ih' =>
    have he : pushforwardMk f hf a.1.1 a.1.2 a.2 = pushforwardMk f hf b.1.1 b.1.2 b.2 :=
      Quot.eqvGen_sound hab
    rw [← he] at ih'
    exact ih.trans ih'

theorem finalOn_pushforwardFinal : FinalOn (pushforwardFinal f hf) Set.univ Set.univ := by
  refine ⟨mapsTo_univ _ _, fun w _ => ?_⟩
  obtain ⟨x, y, h, rfl⟩ := exists_pushforwardMk_eq w
  refine ⟨⟨x, trivial, pushforwardMk_le_pushforwardFinal f hf x y h⟩,
    IsUpperSet.isPreconnected_iff_reflTransGen.2 fun x₁ h₁ x₂ h₂ => ?_⟩
  obtain ⟨h₁', -, he₁⟩ := (pushforwardMk_le_pushforwardMk_iff f hf h le_rfl).1 h₁.2
  obtain ⟨h₂', -, he₂⟩ := (pushforwardMk_le_pushforwardMk_iff f hf h le_rfl).1 h₂.2
  have hr := reflTransGen_of_eqvGen f hf (Quot.eqvGen_exact (he₁.symm.trans he₂))
  rwa [← he₁] at hr

variable {f} in
theorem isClosedMap_pushforwardFinal (hc : IsClosedMap f) :
    IsClosedMap (pushforwardFinal f hf) := by
  refine IsUpperSet.isClosedMap_iff_fibration.2 fun x w hw => ?_
  obtain ⟨y, hy, rfl⟩ := (pf_le_mk_iff _).1 hw
  obtain ⟨x', hx', rfl⟩ := IsUpperSet.isClosedMap_iff_fibration.1 hc hy
  exact ⟨x', hx', Quot.sound ⟨rfl, hx'⟩⟩

end Atoms.Molecule.OGP
