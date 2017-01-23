# Coq Plugin smpl

A plugin that realizes a tactic similar to `first [ l_1 | ... | l_n ]`,
with the twist that the list `l_1 | ... | l_n` can be extended similar to
an eauto database (i.e. works across modules).

The plugin requires Coq 8.6.

See [the included demo file](theories/Demo.v).
