// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2VerifyingKey {
    constructor() {
        assembly {
            {%- for (name, chunk) in constants %}
            mstore({{ (32 * loop.index0)|hex_padded(4) }}, {{ chunk|hex_padded(64) }}) // {{ name }}
            {%- endfor %}
            {%- for (x, y) in fixed_comms %}
            {%- let offset = constants.len() %}
            mstore({{ (32 * (offset + 2 * loop.index0))|hex_padded(4) }}, {{ x|hex_padded(64) }}) // fixed_comms[{{ loop.index0 }}].x
            mstore({{ (32 * (offset + 2 * loop.index0 + 1))|hex_padded(4) }}, {{ y|hex_padded(64) }}) // fixed_comms[{{ loop.index0 }}].y
            {%- endfor %}
            {%- for (x, y) in permutation_comms %}
            {%- let offset = constants.len() + 2 * fixed_comms.len() %}
            mstore({{ (32 * (offset + 2 * loop.index0))|hex_padded(4) }}, {{ x|hex_padded(64) }}) // permutation_comms[{{ loop.index0 }}].x
            mstore({{ (32 * (offset + 2 * loop.index0 + 1))|hex_padded(4) }}, {{ y|hex_padded(64) }}) // permutation_comms[{{ loop.index0 }}].y
            {%- endfor %}

            return(0, {{ (32 * (constants.len() + 2 * fixed_comms.len() + 2 * permutation_comms.len()))|hex() }})
        }
    }
}
