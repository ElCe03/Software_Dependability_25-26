-- phpMyAdmin SQL Dump
-- version 5.2.1
-- https://www.phpmyadmin.net/
--
-- Host: localhost
-- Generation Time: Nov 07, 2025 at 10:13 AM
-- Server version: 10.4.32-MariaDB
-- PHP Version: 8.1.25

SET SQL_MODE = "NO_AUTO_VALUE_ON_ZERO";
START TRANSACTION;
SET time_zone = "+00:00";


/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8mb4 */;

--
-- Database: `appclinique`
--

-- --------------------------------------------------------

--
-- Table structure for table `commande`
--

CREATE SCHEMA `app`;

use app;

CREATE TABLE `commande` (
  `id` int(11) NOT NULL,
  `date_commande` datetime NOT NULL,
  `total_prix` double NOT NULL,
  `status` varchar(255) NOT NULL DEFAULT 'pending',
  `stripe_session_id` varchar(255) DEFAULT NULL,
  `quantite` double NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `commande_medicament`
--

CREATE TABLE `commande_medicament` (
  `commande_id` int(11) NOT NULL,
  `medicament_id` int(11) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `consultation`
--

CREATE TABLE `consultation` (
  `id` int(11) NOT NULL,
  `service_id` int(11) DEFAULT NULL,
  `date` datetime NOT NULL,
  `patient_identifier` varchar(255) NOT NULL,
  `status` varchar(50) NOT NULL,
  `phone_number` varchar(15) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `departement`
--

CREATE TABLE `departement` (
  `id` int(11) NOT NULL,
  `nom` varchar(255) NOT NULL,
  `adresse` varchar(255) NOT NULL,
  `image` varchar(255) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `doctrine_migration_versions`
--

CREATE TABLE `doctrine_migration_versions` (
  `version` varchar(191) NOT NULL,
  `executed_at` datetime DEFAULT NULL,
  `execution_time` int(11) DEFAULT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8 COLLATE=utf8_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `dossier_medicale`
--

CREATE TABLE `dossier_medicale` (
  `id` int(11) NOT NULL,
  `patient_id` int(11) NOT NULL,
  `medecin_id` int(11) NOT NULL,
  `date_de_creation` datetime NOT NULL,
  `historique_des_maladies` longtext DEFAULT NULL,
  `operations_passees` longtext DEFAULT NULL,
  `consultations_passees` longtext DEFAULT NULL,
  `statut_dossier` varchar(255) NOT NULL,
  `notes` longtext DEFAULT NULL,
  `image` varchar(255) DEFAULT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `entretien`
--

CREATE TABLE `entretien` (
  `id` int(11) NOT NULL,
  `equipement_id` int(11) NOT NULL,
  `date` date NOT NULL,
  `description` varchar(255) DEFAULT NULL,
  `nom_equipement` varchar(200) NOT NULL,
  `created_at` datetime NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

--
-- Dumping data for table `entretien`
--

INSERT INTO `entretien` (`id`, `equipement_id`, `date`, `description`, `nom_equipement`, `created_at`) VALUES
(186, 85, '2025-05-08', 'c un entretien pour le RADIO11', 'RADIO', '2025-05-01 21:15:38'),
(187, 86, '2025-05-10', 'pour le test_final1 c a mortie', 'test_final1', '2025-05-01 21:20:47'),
(188, 86, '2025-05-10', 'hhhhhhhhhhhhhhhh', 'test_final1', '2025-05-01 21:50:24'),
(189, 88, '2025-05-20', 'pour le scanner3', 'scanner3..', '2025-05-02 22:25:59'),
(191, 89, '2025-05-29', ',,,,,,,,,,,,,,,,,,,,,,', 'irmm', '2025-05-02 22:39:21'),
(192, 90, '2025-05-04', 'pour l\'oxymetre1', 'Oxymètre', '2025-05-03 07:31:34'),
(194, 94, '2025-05-10', 'pour le irm1111 l\'entretien et apres in va avoir un pdf', 'irm1', '2025-05-03 09:23:59'),
(195, 96, '2025-05-04', 'pour le IRM .....', 'IRM', '2025-05-03 10:19:55'),
(196, 97, '2025-05-08', 'pour le scanner 1', 'Scanner1', '2025-05-03 10:30:43'),
(197, 99, '2025-05-17', 'iiiiiiiii', 'irm11..', '2025-05-07 09:55:19'),
(198, 101, '2025-05-17', 'hhhhhhhhhhhhhhhhhhhhhhhhhhh', 'sedik', '2025-05-07 10:27:03'),
(199, 67, '2025-05-16', 'hhhhhhh', 'Scanner', '2025-05-07 10:48:50'),
(200, 102, '2025-05-24', 'pour le test final', 'TEST FINAL', '2025-05-07 21:44:43');

-- --------------------------------------------------------

--
-- Table structure for table `equipement`
--

CREATE TABLE `equipement` (
  `id` int(11) NOT NULL,
  `nom` varchar(200) NOT NULL,
  `type` varchar(200) NOT NULL,
  `statut` varchar(200) NOT NULL,
  `category` varchar(200) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

--
-- Dumping data for table `equipement`
--

INSERT INTO `equipement` (`id`, `nom`, `type`, `statut`, `category`) VALUES
(67, 'Scanner', 'medicale', 'maintenance', 'Imagerie médicale'),
(77, 'radio1', 'medicale', 'Fonctionnel', 'Imagerie médicale'),
(79, 'radioo111', 'medicale', 'En Panne', 'Imagerie médicale'),
(80, 'scanner2', 'medicale', 'En Panne', 'Imagerie médicale'),
(82, 'IRM', 'medicale', 'En Panne', 'Imagerie médicale'),
(83, 'test++', 'medicale', 'maintenance', 'Imagerie médicale'),
(85, 'RADIO', 'MEDICALE', 'Fonctionnel', 'Imagerie médicale'),
(86, 'test_final1', 'medicale', 'maintenance', 'Imagerie médicale'),
(87, 'Scanner2', 'medicale', 'Fonctionnel', 'Imagerie médicale'),
(88, 'scanner3.', 'medicale', 'maintenance', 'Imagerie médicale'),
(89, 'irmm', 'medicale', 'maintenance', 'Imagerie médicale'),
(90, 'Oxymètre', 'medicale', 'maintenance', 'Imagerie médicale'),
(94, 'irm1', 'medicale1', 'maintenance', 'Imagerie médicale'),
(96, 'IRM', 'medicale', 'maintenance', 'Imagerie médicale'),
(97, 'Scanner1', 'medicale', 'maintenance', 'Imagerie médicale'),
(98, 'irm', 'medicale', 'Fonctionnel', 'Imagerie médicale'),
(99, 'irm11..', 'medicale', 'maintenance', 'Imagerie médicale'),
(100, 'IRMM', 'medicale', 'En Panne', 'Imagerie médicale'),
(101, 'sedik', 'hhhhhhhh', 'maintenance', 'Imagerie médicale'),
(102, 'TEST FINAL', 'medicale', 'maintenance', 'Imagerie médicale');

-- --------------------------------------------------------

--
-- Table structure for table `etage`
--

CREATE TABLE `etage` (
  `id` int(11) NOT NULL,
  `departement_id` int(11) DEFAULT NULL,
  `numero` int(11) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `medicament`
--

CREATE TABLE `medicament` (
  `id` int(11) NOT NULL,
  `nom_medicament` varchar(255) NOT NULL,
  `description_medicament` varchar(255) NOT NULL,
  `type_medicament` varchar(255) NOT NULL,
  `prix_medicament` double NOT NULL,
  `quantite_stock` int(11) NOT NULL,
  `date_entree` datetime NOT NULL,
  `date_expiration` datetime NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `medicament_commande`
--

CREATE TABLE `medicament_commande` (
  `commande_id` int(11) NOT NULL,
  `medicament_id` int(11) NOT NULL,
  `quantite` int(11) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `messenger_messages`
--

CREATE TABLE `messenger_messages` (
  `id` bigint(20) NOT NULL,
  `body` longtext NOT NULL,
  `headers` longtext NOT NULL,
  `queue_name` varchar(190) NOT NULL,
  `created_at` datetime NOT NULL COMMENT '(DC2Type:datetime_immutable)',
  `available_at` datetime NOT NULL COMMENT '(DC2Type:datetime_immutable)',
  `delivered_at` datetime DEFAULT NULL COMMENT '(DC2Type:datetime_immutable)'
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `rapport`
--

CREATE TABLE `rapport` (
  `id` int(11) NOT NULL,
  `entretien_id` int(11) NOT NULL,
  `nom_fichier` varchar(255) NOT NULL,
  `date_creation` datetime NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `reservation`
--

CREATE TABLE `reservation` (
  `id` int(11) NOT NULL,
  `salle_id` int(11) DEFAULT NULL,
  `date_debut` datetime NOT NULL,
  `date_fin` datetime NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `salle`
--

CREATE TABLE `salle` (
  `id` int(11) NOT NULL,
  `etage_id` int(11) DEFAULT NULL,
  `nom` varchar(255) NOT NULL,
  `capacite` int(11) NOT NULL,
  `type_salle` varchar(255) NOT NULL,
  `image` varchar(255) NOT NULL,
  `status` varchar(255) NOT NULL,
  `priorite` int(11) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `sejour`
--

CREATE TABLE `sejour` (
  `id` int(11) NOT NULL,
  `dossier_medicale_id` int(11) NOT NULL,
  `date_entree` datetime NOT NULL,
  `date_sortie` datetime NOT NULL,
  `type_sejour` varchar(255) NOT NULL,
  `frais_sejour` double NOT NULL,
  `moyen_paiement` varchar(255) NOT NULL,
  `statut_paiement` varchar(255) NOT NULL,
  `prix_extras` double DEFAULT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `service`
--

CREATE TABLE `service` (
  `id` int(11) NOT NULL,
  `name` varchar(255) NOT NULL,
  `description` varchar(255) NOT NULL,
  `duration` int(11) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

-- --------------------------------------------------------

--
-- Table structure for table `users`
--

CREATE TABLE `users` (
  `id` int(11) NOT NULL,
  `email` varchar(180) NOT NULL,
  `password` varchar(255) NOT NULL,
  `roles` longtext CHARACTER SET utf8mb4 COLLATE utf8mb4_bin NOT NULL COMMENT '(DC2Type:json)' CHECK (json_valid(`roles`)),
  `nom` varchar(255) NOT NULL,
  `prenom` varchar(255) NOT NULL,
  `type` varchar(255) NOT NULL,
  `specialite` varchar(255) DEFAULT NULL,
  `telephone` varchar(20) DEFAULT NULL,
  `adresse` varchar(255) DEFAULT NULL,
  `date_naissance` date DEFAULT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_unicode_ci;

--
-- Dumping data for table `users`
--

INSERT INTO `users` (`id`, `email`, `password`, `roles`, `nom`, `prenom`, `type`, `specialite`, `telephone`, `adresse`, `date_naissance`) VALUES
(2, 'Meriam.Bouhjar@esprit.tn', '$2y$13$oEUHsgF2j3FRCwZEwB8p3.P93jdyDjgyM.NqxU.40gHagVfzQmF1S', '[\"ROLE_STAFF\",\"ROLE_USER\"]', 'meriam', 'bouhjar', 'staff', NULL, '28545533', NULL, NULL),
(3, 'bouhjarmeriem25@gmail.com', '$2a$12$IMDRt27oEHWP4SYkk3h.3.iuYrDWDbPTCaxhxXec8pvB/06SY2GJG', '[\"ROLE_PATIENT\"]', 'Bouhjar', 'Meriamm', 'PATIENT', NULL, '21007520', 'mercato san severino', '2000-05-05'),
(7, 'Afefguitouni25@gmail.com', '$2a$12$sGoT5K6CH3Z.DsimahuBCucKlkklSVVhnK1bJZ6/ifx1lcyAE/sxm', '[\"ROLE_USER\"]', 'AFEF', 'GUITOUNI', 'ADMIN', NULL, NULL, NULL, NULL);

--
-- Indexes for dumped tables
--

--
-- Indexes for table `commande`
--
ALTER TABLE `commande`
  ADD PRIMARY KEY (`id`);

--
-- Indexes for table `commande_medicament`
--
ALTER TABLE `commande_medicament`
  ADD PRIMARY KEY (`commande_id`,`medicament_id`),
  ADD KEY `IDX_25E5EDC82EA2E54` (`commande_id`),
  ADD KEY `IDX_25E5EDCAB0D61F7` (`medicament_id`);

--
-- Indexes for table `consultation`
--
ALTER TABLE `consultation`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_964685A6ED5CA9E6` (`service_id`);

--
-- Indexes for table `departement`
--
ALTER TABLE `departement`
  ADD PRIMARY KEY (`id`);

--
-- Indexes for table `doctrine_migration_versions`
--
ALTER TABLE `doctrine_migration_versions`
  ADD PRIMARY KEY (`version`);

--
-- Indexes for table `dossier_medicale`
--
ALTER TABLE `dossier_medicale`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_4C53FBC06B899279` (`patient_id`),
  ADD KEY `IDX_4C53FBC04F31A84` (`medecin_id`);

--
-- Indexes for table `entretien`
--
ALTER TABLE `entretien`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_2B58D6DA806F0F5C` (`equipement_id`);

--
-- Indexes for table `equipement`
--
ALTER TABLE `equipement`
  ADD PRIMARY KEY (`id`);

--
-- Indexes for table `etage`
--
ALTER TABLE `etage`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_2DDCF14BCCF9E01E` (`departement_id`);

--
-- Indexes for table `medicament`
--
ALTER TABLE `medicament`
  ADD PRIMARY KEY (`id`);

--
-- Indexes for table `medicament_commande`
--
ALTER TABLE `medicament_commande`
  ADD PRIMARY KEY (`commande_id`,`medicament_id`),
  ADD KEY `IDX_81D516D182EA2E54` (`commande_id`),
  ADD KEY `IDX_81D516D1AB0D61F7` (`medicament_id`);

--
-- Indexes for table `messenger_messages`
--
ALTER TABLE `messenger_messages`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_75EA56E0FB7336F0` (`queue_name`),
  ADD KEY `IDX_75EA56E0E3BD61CE` (`available_at`),
  ADD KEY `IDX_75EA56E016BA31DB` (`delivered_at`);

--
-- Indexes for table `rapport`
--
ALTER TABLE `rapport`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_BE34A09C548DCEA2` (`entretien_id`);

--
-- Indexes for table `reservation`
--
ALTER TABLE `reservation`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_42C84955DC304035` (`salle_id`);

--
-- Indexes for table `salle`
--
ALTER TABLE `salle`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_4E977E5C984CE93F` (`etage_id`);

--
-- Indexes for table `sejour`
--
ALTER TABLE `sejour`
  ADD PRIMARY KEY (`id`),
  ADD KEY `IDX_96F52028F2C46B04` (`dossier_medicale_id`);

--
-- Indexes for table `service`
--
ALTER TABLE `service`
  ADD PRIMARY KEY (`id`);

--
-- Indexes for table `users`
--
ALTER TABLE `users`
  ADD PRIMARY KEY (`id`),
  ADD UNIQUE KEY `UNIQ_1483A5E9E7927C74` (`email`);

--
-- AUTO_INCREMENT for dumped tables
--

--
-- AUTO_INCREMENT for table `commande`
--
ALTER TABLE `commande`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `consultation`
--
ALTER TABLE `consultation`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `departement`
--
ALTER TABLE `departement`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `dossier_medicale`
--
ALTER TABLE `dossier_medicale`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `entretien`
--
ALTER TABLE `entretien`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT, AUTO_INCREMENT=201;

--
-- AUTO_INCREMENT for table `equipement`
--
ALTER TABLE `equipement`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT, AUTO_INCREMENT=103;

--
-- AUTO_INCREMENT for table `etage`
--
ALTER TABLE `etage`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `medicament`
--
ALTER TABLE `medicament`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `messenger_messages`
--
ALTER TABLE `messenger_messages`
  MODIFY `id` bigint(20) NOT NULL AUTO_INCREMENT, AUTO_INCREMENT=5;

--
-- AUTO_INCREMENT for table `rapport`
--
ALTER TABLE `rapport`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `reservation`
--
ALTER TABLE `reservation`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `salle`
--
ALTER TABLE `salle`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `sejour`
--
ALTER TABLE `sejour`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `service`
--
ALTER TABLE `service`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT;

--
-- AUTO_INCREMENT for table `users`
--
ALTER TABLE `users`
  MODIFY `id` int(11) NOT NULL AUTO_INCREMENT, AUTO_INCREMENT=8;

--
-- Constraints for dumped tables
--

--
-- Constraints for table `commande_medicament`
--
ALTER TABLE `commande_medicament`
  ADD CONSTRAINT `FK_25E5EDC82EA2E54` FOREIGN KEY (`commande_id`) REFERENCES `commande` (`id`) ON DELETE CASCADE,
  ADD CONSTRAINT `FK_25E5EDCAB0D61F7` FOREIGN KEY (`medicament_id`) REFERENCES `medicament` (`id`) ON DELETE CASCADE;

--
-- Constraints for table `consultation`
--
ALTER TABLE `consultation`
  ADD CONSTRAINT `FK_964685A6ED5CA9E6` FOREIGN KEY (`service_id`) REFERENCES `service` (`id`);

--
-- Constraints for table `dossier_medicale`
--
ALTER TABLE `dossier_medicale`
  ADD CONSTRAINT `FK_4C53FBC04F31A84` FOREIGN KEY (`medecin_id`) REFERENCES `users` (`id`),
  ADD CONSTRAINT `FK_4C53FBC06B899279` FOREIGN KEY (`patient_id`) REFERENCES `users` (`id`);

--
-- Constraints for table `entretien`
--
ALTER TABLE `entretien`
  ADD CONSTRAINT `FK_2B58D6DA806F0F5C` FOREIGN KEY (`equipement_id`) REFERENCES `equipement` (`id`);

--
-- Constraints for table `etage`
--
ALTER TABLE `etage`
  ADD CONSTRAINT `FK_2DDCF14BCCF9E01E` FOREIGN KEY (`departement_id`) REFERENCES `departement` (`id`);

--
-- Constraints for table `medicament_commande`
--
ALTER TABLE `medicament_commande`
  ADD CONSTRAINT `FK_81D516D182EA2E54` FOREIGN KEY (`commande_id`) REFERENCES `commande` (`id`),
  ADD CONSTRAINT `FK_81D516D1AB0D61F7` FOREIGN KEY (`medicament_id`) REFERENCES `medicament` (`id`);

--
-- Constraints for table `rapport`
--
ALTER TABLE `rapport`
  ADD CONSTRAINT `FK_BE34A09C548DCEA2` FOREIGN KEY (`entretien_id`) REFERENCES `entretien` (`id`);

--
-- Constraints for table `reservation`
--
ALTER TABLE `reservation`
  ADD CONSTRAINT `FK_42C84955DC304035` FOREIGN KEY (`salle_id`) REFERENCES `salle` (`id`);

--
-- Constraints for table `salle`
--
ALTER TABLE `salle`
  ADD CONSTRAINT `FK_4E977E5C984CE93F` FOREIGN KEY (`etage_id`) REFERENCES `etage` (`id`);

--
-- Constraints for table `sejour`
--
ALTER TABLE `sejour`
  ADD CONSTRAINT `FK_96F52028F2C46B04` FOREIGN KEY (`dossier_medicale_id`) REFERENCES `dossier_medicale` (`id`);
COMMIT;

/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
