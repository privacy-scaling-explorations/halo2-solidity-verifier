pragma solidity ^0.8.21;

contract Halo2VerifyingKey {
    constructor() {
        assembly {
            {%- for (name, chunk) in constants %}
            mstore({{ (32 * loop.index0)|hex_padded(4) }}, {{ chunk|hex() }}) // {{ name }}
            {%- endfor %}
            {%- for chunk in fixed_commitments %}
            mstore({{ (32 * (loop.index0 + constants.len()))|hex_padded(4) }}, {{ chunk|hex() }}) // fixed_commitments[{{ loop.index0 / 2 }}].{% if loop.index0 % 2 == 0 %}x{% else %}y{% endif %}
            {%- endfor %}
            {%- for chunk in permutation_commitments %}
            mstore({{ (32 * (loop.index0 + constants.len() + fixed_commitments.len()))|hex_padded(4) }}, {{ chunk|hex() }}) // permutation_commitments[{{ loop.index0 / 2 }}].{% if loop.index0 % 2 == 0 %}x{% else %}y{% endif %}
            {%- endfor %}

            return(0, {{ (32 * (constants.len() + fixed_commitments.len() + permutation_commitments.len()))|hex() }})
        }
    }
}
