import type { Metadata } from 'next';
import { Geist, Geist_Mono } from 'next/font/google';
import './globals.css';
import './exhibits.css';
import './physics.css';
import './themes.css';
import './reader-experience.css';
import './foundations.css';

const geistSans = Geist({
  variable: '--font-geist-sans',
  subsets: ['latin'],
});

const geistMono = Geist_Mono({
  variable: '--font-geist-mono',
  subsets: ['latin'],
});

export const metadata: Metadata = {
  title: 'From Chirality to the Standard Model — An Interactive Exploration',
  description:
    'From Wu’s experiment to a uniqueness and no-go theorem for compact Lie-algebra embeddings. Explore the reductions, E₆ geometry and threefold chiral class.',
  metadataBase: new URL(
    'https://emad-ii.github.io/chirality-standard-model/',
  ),
  alternates: { canonical: 'https://emad-ii.github.io/chirality-standard-model/' },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en" className="dark" data-theme="dark" style={{ colorScheme: 'dark' }}>
      <body
        className={`${geistSans.variable} ${geistMono.variable} antialiased`}
      >
        {children}
      </body>
    </html>
  );
}
