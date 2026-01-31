<?php
header("Access-Control-Allow-Origin: *");
header("Access-Control-Allow-Methods: GET, POST, OPTIONS");
header("Access-Control-Allow-Headers: Content-Type");

$code = isset($_GET["code"]) ? trim($_GET["code"]) : "";
$side = isset($_GET["side"]) ? trim($_GET["side"]) : "";
$move = isset($_GET["move"]) ? trim($_GET["move"]) : "";
$type = $_GET['type'] ?? 'n';  // n / c / d


if($code==="") exit;

$ip = $_SERVER["REMOTE_ADDR"] ?? "unknown";

// simple sanitize
$code = str_replace(["\n","\r","|"], "", $code);
$side = str_replace(["\n","\r","|"], "", $side);
$move = str_replace(["\n","\r","|"], "", $move);
$type = str_replace(["\n","\r","|"], "", $type);
$ip   = str_replace(["\n","\r","|",","], "", $ip);

// save format: code | move | time
$line = date("Y-m-d H:i:s") . "," . $ip . "," . $code . "," . $side . "," . $move . "," . $type . "\n";

file_put_contents("better_moves.txt", $line, FILE_APPEND);

?>
