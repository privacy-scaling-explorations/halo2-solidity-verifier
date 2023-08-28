pragma solidity ^0.8.21;

contract Halo2VerifyingKey {
    constructor() {
        assembly {
            {% for chunk in chunks -%}
            {% let offset = 32 * loop.index0 -%}
            mstore({{ offset|hex_padded(4) }}, {{ chunk|hex() }})
            {% endfor -%}
            {% let length = 32 * chunks.len() -%}
            return(0, {{ length|hex() }})
        }
    }
}
