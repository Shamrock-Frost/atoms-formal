import Mathlib.Data.FinEnum.Option
import Mathlib.Order.TypeTags

namespace WithBot

instance instFinEnum (α : Type*) [FinEnum α] : FinEnum (WithBot α) :=
  inferInstanceAs (FinEnum (Option α))

end WithBot

namespace WithTop

instance instFinEnum (α : Type*) [FinEnum α] : FinEnum (WithTop α) :=
  inferInstanceAs (FinEnum (Option α))

end WithTop
