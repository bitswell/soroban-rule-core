// Integer units are deliberately small: the prototype enumerates closed ranges.
permit (
    principal == Signer::"session",
    action == Action::"guess",
    resource == Contract::"game"
) when { context.guess >= 0 && context.guess <= 9 };

permit (
    principal == Signer::"session",
    action == Action::"transfer",
    resource == Contract::"xlm"
) when {
    context.from == Account::"alice" &&
    context.to == Contract::"game" &&
    context.amount >= 0 && context.amount <= 100 &&
    context.authRootContract == Contract::"game" &&
    context.authRootFunction == "guess"
};
