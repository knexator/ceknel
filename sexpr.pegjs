{
    function listToSexpr(elements) {
        if (elements.length === 0) {
            return {type: "atom", value: "nil"}
        } else {
            return {type: "pair", left: elements[0], right: listToSexpr(elements.slice(1))}
        }
    }

    function listWithSentinelToSexpr(elements, sentinel) {
        if (elements.length === 1) {
            return {type: "pair", left: elements[0], right: sentinel}
        } else {
            return {type: "pair", left: elements[0], right: listWithSentinelToSexpr(elements.slice(1), sentinel)}
        }
    }
}

program = sexpr
sexpr = _ atom:symbol _ { return {type: "atom", value: atom}; }
      / _ "(" left:sexpr "." right:sexpr ")" _ { return {type: "pair", left: left, right: right } }
      / _ "(" list:sexpr|.., _| _ "." _ sentinel:sexpr _  ")" _ { return listWithSentinelToSexpr(list, sentinel) }
      / _ "(" list:sexpr|.., _| ")" _ { return listToSexpr(list) }

symbol     = (! ".") chars: (!delimiter @.)+ { return chars.join("") }
space      = " " / [\n\r\t]
paren      = "(" / ")"
delimiter  = paren / space
_ = space*
