// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.22;

import { WETH } from "solmate/tokens/WETH.sol";
import { Ownable } from "openzeppelin-contracts/contracts/access/Ownable.sol";

contract DemoWETH is WETH, Ownable {
    constructor() WETH() Ownable() { }

    function mint(address to, uint256 amount) external onlyOwner {
        _mint(to, amount);
    }

    function burn(address from, uint256 amount) external onlyOwner {
        _burn(from, amount);
    }
}
