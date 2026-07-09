import Std.Internal.Do
open Std.Internal.Do
-- Is WPConjunctive visible via the plain `Std.Internal.Do` import Ascent uses?
#check @WPConjunctive
#check @WPConjunctive.wp_meet_wp_le
#check @StateT.instWPConjunctive
