import RankCompression
import CanonicalControls

namespace ECC.RankControls
open ECC.CanonicalControls ECC.RankCompression

theorem representative_positions : ((positions word).map Fin.val) = [0, 1, 3] := by decide

theorem compressed_ordinals :
    ((List.finRange 5).map fun t => (encode word t).val) = [0, 1, 0, 2, 1] := by decide

theorem last_ordinal_recovers_position :
    (unrank word ⟨2, by decide⟩).val.val = 3 := by decide

#print axioms representative_positions
#print axioms compressed_ordinals
#print axioms last_ordinal_recovers_position

end ECC.RankControls
