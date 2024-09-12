
# Regex engine in Haskell

This is a simple implementation of a regex engine in Haskell using epsilon-NFAs. It uses the academic syntax for regular expressions, meaning brackets "(...)" to group terms, "*" for the Kleene star and "+" for the union (either or).

It supports matching a whole regex, searching for all occurrences of a regex in a string and splitting a string by a regex pattern.