import Atoms.Serialize.Document

open Atoms.Molecule (FaceData)

namespace Atoms.Serialize

def natToJson (i : ℕ) : Json := .num ⟨(i : Int), 0⟩

def natOfJson : Json → Option ℕ
  | .num n =>
      match normalizeNum n.mantissa n.exponent with
      | (m, 0) => if 0 ≤ m then some m.toNat else none
      | _ => none
  | _ => none

def faceDataToJson (f : FaceData) : Json :=
  .obj [(Document.keyMinus, .arr (f.minus.map natToJson)),
    (Document.keyPlus, .arr (f.plus.map natToJson))]

def faceDataOfJson : Json → Option FaceData := fun j => do
  let fs ← j.asObject
  guard (fs.length = 2 ∧ (fs.map Prod.fst).Nodup)
  let ml ← (← fs.lookup Document.keyMinus).asArray
  let pl ← (← fs.lookup Document.keyPlus).asArray
  let mi ← ml.mapM natOfJson
  let pi ← pl.mapM natOfJson
  some ⟨mi, pi⟩

namespace Document

def toJson (d : Document) : Json :=
  .obj ((keyFormat, .str formatName) :: (keyVersion, natToJson formatVersion) ::
    (keyFaces, .arr (d.faces.map fun row => .arr (row.map faceDataToJson))) ::
    ((match d.labels with
        | none => []
        | some ls => [(keyLabels, .arr (ls.map fun row => .arr (row.map Json.str)))]) ++
      (match d.layout with
        | none => []
        | some l => [(keyLayout, .obj l)]) ++ d.extra))

def ofJson (j : Json) : Option Document := do
  let fs ← j.asObject
  guard ((fs.map Prod.fst).Nodup)
  guard (fs.lookup keyFormat = some (.str formatName))
  guard (natOfJson (← fs.lookup keyVersion) = some formatVersion)
  let rows ← (← fs.lookup keyFaces).asArray
  let faces ← rows.mapM fun row => do
    let cells ← row.asArray
    cells.mapM faceDataOfJson
  let labels ← match fs.lookup keyLabels with
    | none => pure none
    | some j' => do
        let rows' ← j'.asArray
        let ls ← rows'.mapM fun row => do
          let cells ← row.asArray
          cells.mapM Json.asString
        pure (some ls)
  let layout ← match fs.lookup keyLayout with
    | none => pure none
    | some j' => (j'.asObject).map some
  some ⟨⟨faces⟩, labels, layout, fs.filter fun p => decide (p.1 ∉ knownKeys)⟩

def print (d : Document) : List Char := printJson d.toJson

def parse (cs : List Char) : Option Document := (parseJson cs).bind ofJson

def normalize (d : Document) : Document :=
  { d with layout := d.layout.map normalizeFields, extra := normalizeFields d.extra }

private theorem natOfJson_natToJson (i : ℕ) : natOfJson (natToJson i) = some i := by
  simp [natOfJson, natToJson, normalizeNum]

private theorem natOfJson_comp_natToJson : natOfJson ∘ natToJson = some :=
  funext natOfJson_natToJson

private theorem mapM_some {α : Type} (l : List α) : l.mapM some = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

private theorem faceDataOfJson_faceDataToJson (f : FaceData) :
    faceDataOfJson (faceDataToJson f) = some f := by
  have hne : keyMinus ≠ keyPlus := by decide
  have hb : (keyPlus == keyMinus) = false := by decide
  simp [faceDataOfJson, faceDataToJson, Json.asObject, Json.asArray, List.lookup_cons, hne, hb,
    natOfJson_comp_natToJson, mapM_some]

private theorem ofJson_obj {fs : List (JString × Json)} {faces : List (List FaceData)}
    {labels : Option (List (List JString))} {layout : Option (List (JString × Json))}
    (hnodup : (fs.map Prod.fst).Nodup)
    (hformat : fs.lookup keyFormat = some (.str formatName))
    (hversion : fs.lookup keyVersion = some (natToJson formatVersion))
    (hfaces : fs.lookup keyFaces = some (.arr (faces.map fun row => .arr (row.map faceDataToJson))))
    (hlabels : fs.lookup keyLabels =
      labels.map fun ls => .arr (ls.map fun row => .arr (row.map Json.str)))
    (hlayout : fs.lookup keyLayout = layout.map .obj) :
    ofJson (.obj fs) =
      some ⟨⟨faces⟩, labels, layout, fs.filter fun p => decide (p.1 ∉ knownKeys)⟩ := by
  cases labels <;> cases layout <;>
    simp [ofJson, Json.asObject, Json.asArray, Json.asString, hnodup, hformat, hversion, hfaces,
      hlabels, hlayout, natOfJson_natToJson, Function.comp_def, faceDataOfJson_faceDataToJson,
      mapM_some]

private theorem mem_knownKeys : keyFormat ∈ knownKeys ∧ keyVersion ∈ knownKeys ∧
    keyFaces ∈ knownKeys ∧ keyLabels ∈ knownKeys ∧ keyLayout ∈ knownKeys := by
  decide

private theorem keys_ne : keyFormat ≠ keyVersion ∧ keyFormat ≠ keyFaces ∧
    keyFormat ≠ keyLabels ∧ keyFormat ≠ keyLayout ∧ keyVersion ≠ keyFaces ∧
    keyVersion ≠ keyLabels ∧ keyVersion ≠ keyLayout ∧ keyFaces ≠ keyLabels ∧
    keyFaces ≠ keyLayout ∧ keyLabels ≠ keyLayout := by
  decide

private theorem beq_keys : (keyVersion == keyFormat) = false ∧ (keyFaces == keyFormat) = false ∧
    (keyFaces == keyVersion) = false ∧ (keyLabels == keyFormat) = false ∧
    (keyLabels == keyVersion) = false ∧ (keyLabels == keyFaces) = false ∧
    (keyLayout == keyFormat) = false ∧ (keyLayout == keyVersion) = false ∧
    (keyLayout == keyFaces) = false ∧ (keyLayout == keyLabels) = false ∧
    (keyLabels == keyLayout) = false := by
  decide

private theorem ofJson_toJson (d : Document) (hd : d.FreshKeys) : ofJson d.toJson = some d := by
  rcases d with ⟨⟨faces⟩, labels, layout, extra⟩
  obtain ⟨hnodup, hfresh⟩ := hd
  dsimp only at hnodup hfresh
  have hlook : ∀ k ∈ knownKeys, extra.lookup k = none := fun k hk =>
    List.lookup_eq_none_iff.2 fun p hp => bne_iff_ne.2 fun h => hfresh p hp (h ▸ hk)
  have hnot : ∀ k ∈ knownKeys, ∀ x, (k, x) ∉ extra := fun k hk x hx => hfresh _ hx hk
  have hfresh' : ∀ (a : JString) (b : Json), (a, b) ∈ extra → a ∉ knownKeys :=
    fun _ _ h => hfresh _ h
  obtain ⟨hmF, hmV, hmFa, hmL, hmLy⟩ := mem_knownKeys
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ := beq_keys
  obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, n₁₀⟩ := keys_ne
  rw [toJson, ofJson_obj (faces := faces) (labels := labels) (layout := layout) ?_ ?_ ?_ ?_ ?_ ?_]
  · cases labels <;> cases layout <;> simpa [hmF, hmV, hmFa, hmL, hmLy] using hfresh'
  all_goals cases labels <;> cases layout <;>
    simp [List.lookup_cons, hlook _ hmL, hlook _ hmLy, hnodup, hnot _ hmF, hnot _ hmV,
      hnot _ hmFa, hnot _ hmL, hnot _ hmLy, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁, n₁, n₂,
      n₃, n₄, n₅, n₆, n₇, n₈, n₉, n₁₀]

private theorem nodup_and_extra_of_ofJson_eq_some {fs : List (JString × Json)} {d : Document}
    (h : ofJson (.obj fs) = some d) :
    (fs.map Prod.fst).Nodup ∧ d.extra = fs.filter fun p => decide (p.1 ∉ knownKeys) := by
  simp only [ofJson, Json.asObject, Option.bind_eq_bind, Option.bind_some,
    Option.bind_eq_some_iff] at h
  obtain ⟨u, hg, -, -, -, -, -, -, -, -, -, -, faces, -, hrest⟩ := h
  have key : ∀ {labels : Option (List (List JString))} {layout : Option (List (JString × Json))},
      some ⟨⟨faces⟩, labels, layout, fs.filter fun p => decide (p.1 ∉ knownKeys)⟩ = some d →
        d.extra = fs.filter fun p => decide (p.1 ∉ knownKeys) := fun h => by
    rw [← Option.some.inj h]
  refine ⟨by_contra fun hn => ?_, ?_⟩
  · rw [guard, if_neg hn] at hg
    cases hg
  split at hrest
  · rw [Option.pure_def, Option.bind_some] at hrest
    split at hrest
    · rw [Option.pure_def, Option.bind_some] at hrest
      exact key hrest
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 hrest
      exact key h
  · obtain ⟨_, -, h₁⟩ := Option.bind_eq_some_iff.1 hrest
    obtain ⟨_, -, h₂⟩ := Option.bind_eq_some_iff.1 h₁
    rw [Option.pure_def, Option.bind_some] at h₂
    split at h₂
    · rw [Option.pure_def, Option.bind_some] at h₂
      exact key h₂
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h₂
      exact key h

private theorem normalizeJson_toJson (d : Document) :
    normalizeJson d.toJson = d.normalize.toJson := by
  rcases d with ⟨⟨faces⟩, labels, layout, extra⟩
  cases labels <;> cases layout <;>
    simp [toJson, normalize, normalizeJson, natToJson, normalizeNumber, normalizeNum,
      faceDataToJson, Function.comp_def]

private theorem freshKeys_normalize {d : Document} : d.normalize.FreshKeys ↔ d.FreshKeys := by
  have hk : d.normalize.extra.map Prod.fst = d.extra.map Prod.fst := by
    simp [normalize, Function.comp_def]
  have hm : ∀ k, k ∈ d.normalize.extra.map Prod.fst ↔ k ∈ d.extra.map Prod.fst := by
    rw [hk]
    exact fun _ => Iff.rfl
  rw [FreshKeys, FreshKeys, hk]
  refine and_congr_right fun _ => ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · obtain ⟨q, hq, hqp⟩ := List.mem_map.1 ((hm p.1).2 (List.mem_map_of_mem hp))
    exact hqp ▸ h q hq
  · obtain ⟨q, hq, hqp⟩ := List.mem_map.1 ((hm p.1).1 (List.mem_map_of_mem hp))
    exact hqp ▸ h q hq

theorem parse_print (d : Document) (hd : d.FreshKeys) : parse d.print = some d.normalize := by
  rw [parse, print, parseJson_printJson, Option.bind_some, normalizeJson_toJson]
  exact ofJson_toJson _ (freshKeys_normalize.2 hd)

theorem parse_print_eq_some_iff (d : Document) :
    parse d.print = some d ↔ d.FreshKeys ∧ d.normalize = d := by
  refine ⟨fun h => ?_, fun ⟨hd, hn⟩ => by rw [parse_print d hd, hn]⟩
  have hd : d.FreshKeys := by
    have h' := h
    rw [parse, print, parseJson_printJson, Option.bind_some, normalizeJson_toJson, toJson] at h'
    obtain ⟨hnodup, hextra⟩ := nodup_and_extra_of_ofJson_eq_some h'
    refine ⟨?_, fun p hp => ?_⟩
    · rw [hextra]
      exact hnodup.sublist ((List.filter_sublist).map _)
    · rw [hextra] at hp
      exact of_decide_eq_true (List.mem_filter.1 hp).2
  exact ⟨hd, Option.some.inj ((parse_print d hd).symm.trans h)⟩

theorem print_of_parse_print {d d' : Document} (hd : d.FreshKeys) (h : parse d.print = some d') :
    d'.print = d.print := by
  rw [parse_print d hd, Option.some.injEq] at h
  rw [← h, print, print, ← normalizeJson_toJson, printJson_normalizeJson]

end Document

end Atoms.Serialize
